import Mathlib
import RootSystem.SylvesterCriterion.SylvesterForward
import RootSystem.SylvesterCriterion.SylvesterBackward

open Matrix
open BigOperators

/-!
# Sylvester's Criterion (シルベスターの判定法)

A Hermitian (real symmetric) matrix M is positive definite if and only if
all of its leading principal minors are positive.

The k-th leading principal minor of M is the determinant of the upper-left
k×k submatrix of M.

## Main result

- `sylvester_criterion`: The biconditional statement of Sylvester's criterion.
-/

/-- **Sylvester's criterion**: A real symmetric matrix is positive definite if and only if
all its leading principal minors (determinants of upper-left k×k submatrices) are positive. -/
theorem sylvester_criterion {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    M.PosDef ↔ ∀ (k : ℕ) (hk : k ≤ n), 0 < k → 0 < (M.leadingSubmatrix k hk).det :=
  ⟨fun hpd k hk _ => posDef_leading_minors_pos hpd k hk,
   fun hminors => leading_minors_pos_implies_posDef M hM hminors⟩
