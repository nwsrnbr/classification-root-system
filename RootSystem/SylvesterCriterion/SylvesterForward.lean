import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

open Matrix
open Finset
open BigOperators

set_option maxHeartbeats 800000

/-!
# Sylvester's Criterion - Forward Direction

A positive definite matrix has positive leading principal minors.
-/

variable {n : ℕ}

/-- The leading principal submatrix of order k, i.e., the upper-left k×k submatrix. -/
noncomputable def Matrix.leadingSubmatrix (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) ℝ :=
  M.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-
A submatrix of a Hermitian matrix via an injective map is Hermitian.
-/
lemma IsHermitian.submatrix_injective {m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (e : Fin m → Fin n) :
    (M.submatrix e e).IsHermitian := by
  exact IsHermitian.submatrix hM e

/-
A submatrix of a positive definite real matrix via an injective map is positive definite.
-/
lemma PosDef.submatrix_injective {m : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (e : Fin m → Fin n) (he : Function.Injective e) :
    (M.submatrix e e).PosDef := by
  refine' ⟨ _, fun x hx => _ ⟩;
  · convert IsHermitian.submatrix_injective hM.1 e using 1;
  · -- By the properties of the quadratic form and the injectivity of $e$, we can relate the quadratic form of $M.submatrix e e$ with $x$ to the quadratic form of $M$ with a suitable vector $y$.
    have h_quad_form : ∃ y : Fin n → ℝ, (∑ i, ∑ j, star (x i) * (M.submatrix e e i j) * (x j)) = (∑ i, ∑ j, star (y i) * M i j * (y j)) ∧ y ≠ 0 := by
      refine' ⟨ fun i => if hi : ∃ j, e j = i then x ( Classical.choose hi ) else 0, _, _ ⟩ <;> simp_all +decide;
      · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image e Finset.univ ) ) ];
        · rw [ Finset.sum_image <| by tauto ];
          refine' Finset.sum_congr rfl fun i hi => _;
          rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image e Finset.univ ) ) ];
          · rw [ Finset.sum_image ];
            · simp +decide [ he.eq_iff ];
            · exact he.injOn;
          · aesop;
        · aesop;
      · contrapose! hx;
        ext i; replace hx := congr_fun hx ( e i ) ; simp_all +decide [ he.eq_iff ] ;
    simp_all +decide [ Finsupp.sum_fintype ];
    obtain ⟨ y, hy ⟩ := h_quad_form;
    have := hM.2;
    convert this ( show ( Finsupp.equivFunOnFinite.symm y ) ≠ 0 from by simpa [ funext_iff, Finsupp.ext_iff ] using hy.2 ) using 1;
    simp +decide [ Finsupp.sum_fintype, hy ]

/-
Forward direction: A positive definite matrix has positive leading principal minors.
-/
theorem posDef_leading_minors_pos {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (k : ℕ) (hk : k ≤ n) :
    0 < (M.leadingSubmatrix k hk).det := by
  convert Matrix.PosDef.det_pos _;
  convert PosDef.submatrix_injective hM ( Fin.castLE hk ) ( Fin.castLE_injective hk )
