import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

import Mathlib.Data.Matrix.Cartan

variable {ι E F : Type*} [DecidableEq ι]

noncomputable def SymmMatrix (C : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  Matrix.of fun i j : ι ↦
    if i = j then 2
    else -√(C i j * C j i)

variable {E F : Type*}
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (P : RootPairing ι ℝ E F) [P.IsCrystallographic] (b : P.Base)

namespace RootCartan

/-- The symmetrised matrix of any integer matrix is symmetric, hence Hermitian over `ℝ`. -/
lemma symmMatrix_isHermitian (C : Matrix ι ι ℤ) : (SymmMatrix C).IsHermitian := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [SymmMatrix, h, Ne.symm h, mul_comm]

section Finite

variable [Fintype ι]

omit [DecidableEq ι] [P.IsCrystallographic] in
/-- The root form is positive on each root of a finite root pairing over `ℝ`. -/
lemma rootForm_root_self_pos (i : ι) : 0 < P.RootForm (P.root i) (P.root i) :=
  P.rootForm_pos_of_ne_zero (Submodule.subset_span (Set.mem_range_self i)) (P.ne_zero i)

omit [DecidableEq ι] [P.IsCrystallographic] in
lemma two_mul_rootForm_root_root (i j : ι) :
    2 * P.RootForm (P.root i) (P.root j) = P.pairing i j * P.RootForm (P.root j) (P.root j) :=
  P.toInvariantForm.two_mul_apply_root_root i j

omit [DecidableEq ι] in
lemma pairing_nonpos_of_ne {i j : b.support} (hij : i ≠ j) : P.pairing i j ≤ 0 := by
  have h := b.cartanMatrix_le_zero_of_ne i j hij
  rw [← RootPairing.Base.algebraMap_cartanMatrixIn_apply ℤ b i j]
  simpa using h

omit [DecidableEq ι] in
lemma rootForm_root_root_nonpos {i j : b.support} (hij : i ≠ j) :
    P.RootForm (P.root i) (P.root j) ≤ 0 := by
  have h2 := two_mul_rootForm_root_root P (i : ι) (j : ι)
  have hc := rootForm_root_self_pos P (j : ι)
  have hp := pairing_nonpos_of_ne P b hij
  nlinarith [h2, hc, hp]

/-- The entries of the symmetrised Cartan matrix are the Gram matrix entries of the
normalised simple roots. -/
lemma symmMatrix_cartanMatrix_apply (i j : b.support) :
    SymmMatrix b.cartanMatrix i j =
      2 * P.RootForm (P.root i) (P.root j) /
        (√(P.RootForm (P.root i) (P.root i)) * √(P.RootForm (P.root j) (P.root j))) := by
  have ha := rootForm_root_self_pos P (i : ι)
  have hc := rootForm_root_self_pos P (j : ι)
  have hsa0 : 0 < √(P.RootForm (P.root i) (P.root i)) := Real.sqrt_pos.mpr ha
  have hsc0 : 0 < √(P.RootForm (P.root j) (P.root j)) := Real.sqrt_pos.mpr hc
  have hsa : √(P.RootForm (P.root i) (P.root i)) * √(P.RootForm (P.root i) (P.root i))
      = P.RootForm (P.root i) (P.root i) := Real.mul_self_sqrt ha.le
  have hsc : √(P.RootForm (P.root j) (P.root j)) * √(P.RootForm (P.root j) (P.root j))
      = P.RootForm (P.root j) (P.root j) := Real.mul_self_sqrt hc.le
  rcases eq_or_ne i j with rfl | hij
  · have : SymmMatrix b.cartanMatrix i i = 2 := by simp [SymmMatrix]
    rw [this, hsa]
    field_simp
  · have hm := rootForm_root_root_nonpos P b hij
    have h1 := two_mul_rootForm_root_root P (i : ι) (j : ι)
    have h2 := two_mul_rootForm_root_root P (j : ι) (i : ι)
    have hsymm : P.RootForm (P.root j) (P.root i) = P.RootForm (P.root i) (P.root j) :=
      P.rootForm_symmetric.eq (P.root j) (P.root i)
    have hci : ((b.cartanMatrix i j : ℤ) : ℝ) = P.pairing i j := by
      simpa using RootPairing.Base.algebraMap_cartanMatrixIn_apply ℤ b i j
    have hcj : ((b.cartanMatrix j i : ℤ) : ℝ) = P.pairing j i := by
      simpa using RootPairing.Base.algebraMap_cartanMatrixIn_apply ℤ b j i
    have ht : 0 ≤ -(2 * P.RootForm (P.root i) (P.root j)) /
        (√(P.RootForm (P.root i) (P.root i)) * √(P.RootForm (P.root j) (P.root j))) :=
      div_nonneg (by linarith) (by positivity)
    have hsq : ((b.cartanMatrix i j : ℤ) : ℝ) * ((b.cartanMatrix j i : ℤ) : ℝ)
        = (-(2 * P.RootForm (P.root i) (P.root j)) /
          (√(P.RootForm (P.root i) (P.root i)) * √(P.RootForm (P.root j) (P.root j))))^2 := by
      rw [hci, hcj, div_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hc.le]
      rw [eq_div_iff (by positivity)]
      nlinarith [h1, h2, hsymm]
    simp only [SymmMatrix, Matrix.of_apply, if_neg hij]
    rw [hsq, Real.sqrt_sq ht]
    field_simp

open Matrix in
lemma root_cartan_pos_aux : (SymmMatrix b.cartanMatrix).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨symmMatrix_isHermitian _, ?_⟩
  intro x hx
  set f : b.support → ℝ := fun i ↦ x i / √(P.RootForm (P.root i) (P.root i)) with hf
  set v : E := ∑ i : b.support, f i • P.root i with hv
  have hRF : P.RootForm v v =
      ∑ i : b.support, ∑ j : b.support, f i * f j * P.RootForm (P.root i) (P.root j) := by
    simp only [hv, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hs : P.RootForm (P.root (j : ι)) (P.root (i : ι))
        = P.RootForm (P.root (i : ι)) (P.root (j : ι)) := P.rootForm_symmetric.eq _ _
    rw [hs]
  have hval : star x ⬝ᵥ ((SymmMatrix b.cartanMatrix) *ᵥ x) = 2 * P.RootForm v v := by
    rw [hRF, Finset.mul_sum]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [symmMatrix_cartanMatrix_apply P b i j]
    have hi : √(P.RootForm (P.root i) (P.root i)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (rootForm_root_self_pos P (i : ι)))
    have hj : √(P.RootForm (P.root j) (P.root j)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (rootForm_root_self_pos P (j : ι)))
    simp only [hf]
    field_simp
  have hvmem : v ∈ P.rootSpan ℝ :=
    Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))
  have hvne : v ≠ 0 := by
    intro h0
    apply hx
    classical
    set g : ι → ℝ := fun i ↦ if h : i ∈ b.support then f ⟨i, h⟩ else 0 with hg
    have hsum : ∑ i ∈ b.support, g i • P.root i = 0 := by
      rw [← h0, hv, Finset.univ_eq_attach, ← Finset.sum_attach b.support fun i ↦ g i • P.root i]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    have hzero := (linearIndepOn_iff'.mp b.linearIndepOn_root) b.support g (by simp) hsum
    funext i
    have h1 : g i = 0 := hzero i i.2
    have h2 : f i = 0 := by simpa [hg, i.2] using h1
    have hi : √(P.RootForm (P.root i) (P.root i)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (rootForm_root_self_pos P (i : ι)))
    have : x i / √(P.RootForm (P.root i) (P.root i)) = 0 := h2
    field_simp at this
    simpa using this
  rw [hval]
  have := P.rootForm_pos_of_ne_zero hvmem hvne
  linarith

end Finite

end RootCartan

/-
The statement below is the one that was originally posed.  As stated it is **false**: nothing in
the hypotheses forces the index type `ι` (i.e. the set of roots) to be finite, and for infinite
crystallographic root pairings the symmetrised Cartan matrix of a base need not be positive
definite.  For instance the affine root pairing of type `A₁⁽¹⁾` (realised in a three-dimensional
space, with roots `±α + nδ`, `n ∈ ℤ`) has a base `{α, δ - α}` whose Cartan matrix is
`!![2, -2; -2, 2]`; the corresponding symmetrised matrix `!![2, -2; -2, 2]` kills the vector
`(1, 1)` and hence is only positive *semi*definite.  This counterexample is constructed and
verified in `Counterexample.lean`, see `AffineA1.symmMatrix_cartanMatrix_not_posDef`.

-- lemma root_cartan_pos : (SymmMatrix b.cartanMatrix).PosDef := by
--   sorry
-/

/-- **Positive definiteness of the symmetrised Cartan matrix.**

For a crystallographic root pairing with a *finite* set of roots, the symmetrised Cartan matrix
of any base is positive definite.

This is the original statement `root_cartan_pos` with the extra hypothesis `[Finite ι]`, which is
necessary: see the comment above, and `AffineA1.symmMatrix_cartanMatrix_not_posDef` in
`Counterexample.lean`, for an affine root pairing showing that the statement fails without it. -/
theorem root_cartan_pos [Finite ι] : (SymmMatrix b.cartanMatrix).PosDef := by
  have : Fintype ι := Fintype.ofFinite ι
  exact RootCartan.root_cartan_pos_aux P b
