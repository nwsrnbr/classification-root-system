import Mathlib
import RootSystem.SylvesterCriterion.SylvesterForward
import RootSystem.SylvesterCriterion.SchurComplement

open Matrix
open Finset
open BigOperators

set_option maxHeartbeats 1600000

/-!
# Sylvester's Criterion - Backward Direction

If a Hermitian (real symmetric) matrix has all positive leading principal minors,
then it is positive definite. The proof proceeds by induction on the matrix size.
-/

variable {n : ℕ}

/-- The leading submatrix of a leading submatrix is a leading submatrix of the original. -/
lemma leadingSubmatrix_leadingSubmatrix (M : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (j : ℕ) (hk : k ≤ n) (hj : j ≤ k) :
    (M.leadingSubmatrix k hk).leadingSubmatrix j hj = M.leadingSubmatrix j (le_trans hj hk) :=
  Matrix.ext fun i j => by simp +decide [Matrix.leadingSubmatrix]

/-- Backward direction: If all leading principal minors of a symmetric matrix are positive,
    then the matrix is positive definite. -/
theorem leading_minors_pos_implies_posDef
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian)
    (hminors : ∀ (k : ℕ) (hk : k ≤ n), 0 < k → 0 < (M.leadingSubmatrix k hk).det) :
    M.PosDef := by
  induction n with
  | zero =>
    constructor
    · exact hM
    · intro x hx; exact absurd (Subsingleton.elim x 0) hx
  | succ n ih =>
    apply posDef_of_leading_submatrix_posDef_and_det_pos M hM
    · apply ih
      · exact IsHermitian.submatrix_injective hM (Fin.castLE (Nat.le_succ n))
      · intro k hk hk0
        rw [leadingSubmatrix_leadingSubmatrix]
        exact hminors k (le_trans hk (Nat.le_succ n)) hk0
    · convert hminors (n + 1) le_rfl (Nat.succ_pos _)
