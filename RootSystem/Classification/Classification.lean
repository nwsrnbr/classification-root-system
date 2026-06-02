import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.Data.Matrix.Cartan
import Mathlib.Combinatorics.SimpleGraph.Basic
import RootSystem.SymmMatrix.PosDef

namespace CartanMatrix

open Matrix

section SubGraph

variable {n : ℕ}

def LowerLabel (C : Matrix (Fin n) (Fin n) ℤ) :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else
      match C i j with
      | -1 => -1
      | -2 => -1
      | -3 => -2
      | _ => 0

theorem sub_of_pos_def (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (h : (SymmMatrix C).PosDef) :
    (SymmMatrix (isTopLeftBlock C)).PosDef := by
  rw [isTopLeftBlock_eq, ← SymmMatrix_leadingSubmatrix_comm]
  apply PosDef.submatrix_injective h
  apply Fin.castLE_injective

theorem sub_of_pos_def' (C : Matrix (Fin n) (Fin n) ℤ) (h : (SymmMatrix C).PosDef) :
    (SymmMatrix (LowerLabel C)).PosDef := by
  contrapose! h
  simp_all [PosDef]
  intro hH
  rcases h (by apply SymmMatrix_isSymm) with ⟨x, xnz, hx⟩
  let y : Fin n → ℝ := fun i ↦ |x i|
  use Finsupp.equivFunOnFinite.symm y
  split_ands
  · contrapose! xnz
    ext i
    --simp [y] at *
    simp
    rw [← abs_eq_zero]
    calc
      _ = y i := by simp [y]
      _ = (0 : Fin n →₀ ℝ) i := by simp [← xnz]
      _ = 0 := by simp
  · simp [Finsupp.sum_fintype]
    calc
      _ = ∑ (i : Fin n), ∑ (j : Fin n), |x i| * SymmMatrix C i j * |x j| := by
        simp [y, mul_assoc]
      _ ≤ ∑ (i : Fin n), ∑ (j : Fin n), |x i| * SymmMatrix (LowerLabel C) i j * |x j| := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_right
        apply mul_le_mul_of_nonneg_left
        · simp [SymmMatrix, LowerLabel]
          split_ifs
          · rfl
          · aesop
          · have : √2 * √3 = √6 := by rw [← Real.sqrt_mul zero_le_two]; norm_num
            split
            <;> split
            <;> simp [*, mul_comm]
            <;> norm_num
        all_goals apply abs_nonneg
      _ = ∑ (i : Fin n), ∑ (j : Fin n), SymmMatrix (LowerLabel C) i j * |x i * x j| := by
        grind
      _ ≤ ∑ (i : Fin n), ∑ (j : Fin n), SymmMatrix (LowerLabel C) i j * (x i * x j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        by_cases hij : i = j
        · simp [hij]
        · apply mul_le_mul_of_nonpos_left
          · apply le_abs_self
          · simp [SymmMatrix, hij]
      _ = ∑ (i : Fin n), ∑ (j : Fin n), x i * (SymmMatrix (LowerLabel C) i j * x j) := by
        grind
      _ ≤ 0 := by
        simp [Finsupp.sum_fintype] at hx
        grind

end SubGraph

open Matrix

variable {n : ℕ}

lemma PsDf (X : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : X.IsSymm) (hd : ∀ i, X i i = 2) (hsimp : X.IsSimplyLaced) (hp : X.PosDef) :
    X = A n ∨
    X = D n ∨
    (∃ (e : Fin 6 ≃ Fin n), X = (E₆.reindex e e)) ∨
    (∃ (e : Fin 7 ≃ Fin n), X = (E₇.reindex e e)) ∨
    (∃ (e : Fin 8 ≃ Fin n), X = (E₈.reindex e e)) := by
  by_cases hn0 : n = 0
  · left
    ext i j
    cases hn0
    apply Fin.elim0 i
  by_cases hn1 : n = 1
  · left
    ext i j
    cases hn1
    have : i = j := by aesop
    simp [this, hd, A]
  by_cases hn2 : n = 2
  · sorry
  sorry










namespace RootSystem

open RootPairing.Base

variable {ι E F : Type*} [Nonempty ι] [DecidableEq ι] [Finite ι]
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (Φ : RootPairing ι ℝ E F) [Φ.IsRootSystem] [Φ.IsCrystallographic]
  {b : Φ.Base} (h_irred : Φ.IsIrreducible)

#check RootPairing.InvariantForm.form

variable (S : Type*) [CommRing S] [Algebra S ℝ]

/-
lemma cartanMatrixIn_mul_diagonal_eq {P : RootPairing ι ℝ E F} [P.IsRootSystem] [P.IsValuedIn S] [P.IsCrystallographic]
    (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] :
    (b.cartanMatrix).map (algebraMap ℤ ℝ) *
      (Matrix.diagonal fun i : b.support ↦ B.form (P.root i) (P.root i)) =
      (2 : ℝ) • B.form.toMatrix b.toWeightBasis := by
  sorry
-/

lemma isPosDef (B : Φ.InvariantForm) :
    let n := Fintype.card b.support
    let e : b.support ≃ Fin n := Fintype.equivFin _
    (SymmMatrix (b.cartanMatrix.reindex e e)).PosDef := by
  let n := Fintype.card b.support
  let e : b.support ≃ Fin n := Fintype.equivFin _
  let C := (b.cartanMatrix.reindex e e)
  let D := Matrix.diagonal fun i ↦ (B.form (Φ.root i)) (Φ.root i)
  simp [cartanMatrix, cartanMatrixIn]
  show (SymmMatrix C).PosDef
  have : ∃ A D, (SymmMatrix C) = (A * D) * (A * D).transpose := by sorry
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  split_ands
  · apply SymmMatrix_isSymm
  · intro x hx
    rcases this with ⟨A, D, H⟩
    simp [H]
    sorry

/-

  have : (b.cartanMatrix).map (algebraMap ℤ ℝ) * D = 2 • (LinearMap.BilinForm.toMatrix b.toWeightBasis) B.form := by
    rw []

  have := cartanMatrixIn_mul_diagonal_eq ℤ B b
  simp [d] at this

  have : (SymmMatrix C) =
-/



theorem classification (n : ℕ) :
  (∃ (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((A n).reindex σ σ)) ∨
  (∃ (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((B n).reindex σ σ)) ∨
  (∃ (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((C n).reindex σ σ)) ∨
  (∃ (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((D n).reindex σ σ)) ∨
  (∃ (σ : Fin 6 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₆).reindex σ σ)) ∨
  (∃ (σ : Fin 7 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₇).reindex σ σ)) ∨
  (∃ (σ : Fin 8 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₈).reindex σ σ)) ∨
  (∃ (σ : Fin 4 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((F₄).reindex σ σ)) ∨
  (∃ (σ : Fin 2 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((G₂).reindex σ σ)) := by
  classical
  --let n := Fintype.card b.support
  let e : b.support ≃ Fin n := Fintype.equivFin _
  have : n ≠ 0 := by
      --simp only [n]
      apply Finset.Nonempty.card_ne_zero
      simp
      apply b.support_nonempty
  by_cases h1 : n = 1
  · sorry
  sorry



end RootSystem
end CartanMatrix
