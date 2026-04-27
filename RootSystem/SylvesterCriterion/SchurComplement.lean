import Mathlib
import RootSystem.SylvesterCriterion.SylvesterForward

open Matrix
open Finset
open BigOperators

set_option maxHeartbeats 1600000

/-!
# Schur complement argument for the inductive step of Sylvester's criterion

We prove that if M is a real symmetric (n+1)×(n+1) matrix whose leading n×n
submatrix A is positive definite and det M > 0, then M is positive definite.
-/

variable {n : ℕ}

/-- Extract the last column (excluding last entry) of a (n+1)×(n+1) matrix. -/
noncomputable def lastCol (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Fin n → ℝ :=
  fun i => M (Fin.castSucc i) (Fin.last n)

/-- Extract the bottom-right entry of a (n+1)×(n+1) matrix. -/
noncomputable def lastEntry (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  M (Fin.last n) (Fin.last n)

/-- The Schur complement: c - bᵀ A⁻¹ b where M = [[A, b], [bᵀ, c]]. -/
noncomputable def schurComplement (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  lastEntry M - dotProduct (lastCol M) (mulVec (M.leadingSubmatrix n (Nat.le_succ n))⁻¹ (lastCol M))

/-
For a symmetric matrix M, the quadratic form on Fin (n+1) can be decomposed as:
    vᵀMv = xᵀAx + 2t(bᵀx) + ct²
    where v = (x, t), A is the leading submatrix, b is the last column, c is the last entry.
-/
lemma quadratic_form_decomp (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hM : M.IsHermitian) (v : Fin (n+1) → ℝ) :
    dotProduct v (mulVec M v) =
    dotProduct (v ∘ Fin.castSucc) (mulVec (M.leadingSubmatrix n (Nat.le_succ n)) (v ∘ Fin.castSucc))
    + 2 * (v (Fin.last n)) * dotProduct (lastCol M) (v ∘ Fin.castSucc)
    + lastEntry M * (v (Fin.last n))^2 := by
  -- By definition of matrix multiplication and the properties of the dot product, we can expand both sides.
  have h_expand : v ⬝ᵥ M.mulVec v = ∑ i : Fin n, ∑ j : Fin n, v (Fin.castSucc i) * M (Fin.castSucc i) (Fin.castSucc j) * v (Fin.castSucc j) + ∑ i : Fin n, v (Fin.castSucc i) * M (Fin.castSucc i) (Fin.last n) * v (Fin.last n) + ∑ j : Fin n, v (Fin.last n) * M (Fin.last n) (Fin.castSucc j) * v (Fin.castSucc j) + v (Fin.last n) * M (Fin.last n) (Fin.last n) * v (Fin.last n) := by
    simp +decide [ Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc ];
    simp +decide [ mul_add, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_add_distrib ] ; ring;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, dotProduct ];
  simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, add_assoc, pow_two, lastCol, lastEntry ];
  simp +decide [ ← add_assoc, ← mul_assoc, mul_two, Matrix.leadingSubmatrix ];
  simp +decide [ mul_add, add_assoc, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Fin.castLE ];
  congr! 3;
  · ring!;
  · exact hM.apply _ _ ▸ rfl

/-
Completing the square: the quadratic form equals
    (x + t A⁻¹ b)ᵀ A (x + t A⁻¹ b) + s t²
    where s is the Schur complement.
-/
lemma quadratic_form_complete_square (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hM : M.IsHermitian)
    (hA : (M.leadingSubmatrix n (Nat.le_succ n)).PosDef)
    (v : Fin (n+1) → ℝ) :
    dotProduct v (mulVec M v) =
    dotProduct (v ∘ Fin.castSucc + v (Fin.last n) • mulVec (M.leadingSubmatrix n (Nat.le_succ n))⁻¹ (lastCol M))
              (mulVec (M.leadingSubmatrix n (Nat.le_succ n))
                      (v ∘ Fin.castSucc + v (Fin.last n) • mulVec (M.leadingSubmatrix n (Nat.le_succ n))⁻¹ (lastCol M)))
    + schurComplement M * (v (Fin.last n))^2 := by
  rw [ quadratic_form_decomp, schurComplement ];
  · simp +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ];
    by_cases h : IsUnit ( M.leadingSubmatrix n ( Nat.le_succ n ) ).det <;> simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit ];
    · simp +decide [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, dotProduct_comm ] ; ring;
      have := hA.1; simp_all +decide [ Matrix.IsHermitian] ;
      ring;
    · exact absurd h ( hA.det_pos.ne' );
  · assumption

/-
The Schur complement is positive when A is PosDef and det M > 0.
-/
lemma schur_complement_pos (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hM : M.IsHermitian)
    (hA : (M.leadingSubmatrix n (Nat.le_succ n)).PosDef)
    (hdet : 0 < M.det) :
    0 < schurComplement M := by
  -- Use the Schur complement formula for block matrix determinants. We need to show:
  -- det M = det A * schurComplement M
  have det_formula : M.det = (M.leadingSubmatrix n (Nat.le_succ n)).det * schurComplement M := by
    -- Write M as a block matrix:
    set A : Matrix (Fin n) (Fin n) ℝ := M.leadingSubmatrix n (Nat.le_succ n)
    set b : Fin n → ℝ := lastCol M
    set c : ℝ := lastEntry M;
    have h_det : M.det = (M.leadingSubmatrix n (Nat.le_succ n)).det * (c - dotProduct b (mulVec (M.leadingSubmatrix n (Nat.le_succ n))⁻¹ b)) := by
      have h_inv : Invertible A := by
        exact hA.isUnit.invertible
      have h_det_block : M.det = Matrix.det (Matrix.fromBlocks A (Matrix.of (fun i j => b i)) (Matrix.of (fun i j => b j)) (Matrix.of ![![c]])) := by
        convert rfl;
        convert Matrix.det_reindex_self _ _;
        rotate_left;
        all_goals try infer_instance;
        exact?;
        ext i j; simp +decide [ finSumFinEquiv ] ;
        rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> norm_num [ Fin.castAdd, Fin.natAdd ];
        · rfl;
        · rfl;
        · exact hM.apply _ _ ▸ rfl;
        · rfl;
      rw [ h_det_block, Matrix.det_fromBlocks₁₁ ];
      norm_num [ Matrix.mul_assoc, Matrix.mulVec, dotProduct ];
      rfl;
    exact h_det;
  nlinarith [ hA.det_pos ]

/-
The quadratic form of a PosDef matrix is nonneg for all vectors.
-/
lemma posDef_dotProduct_nonneg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.PosDef) (x : Fin k → ℝ) :
    0 ≤ dotProduct x (mulVec A x) := by
  have := hA.2;
  contrapose! this;
  refine' ⟨ Finsupp.equivFunOnFinite.symm x, _, _ ⟩ <;> simp_all +decide [ Finsupp.sum_fintype ];
  · intro h; simp_all +decide [ Finsupp.ext_iff ];
    norm_num [ show x = 0 from funext h ] at this;
  · simpa only [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc ] using this.le

/-
The key inductive step: a symmetric (n+1)×(n+1) matrix with PosDef leading
    submatrix and positive determinant is PosDef.
-/
theorem posDef_of_leading_submatrix_posDef_and_det_pos
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.IsHermitian)
    (hA : (M.leadingSubmatrix n (Nat.le_succ n)).PosDef)
    (hdet : 0 < M.det) :
    M.PosDef := by
  -- Let's decompose the quadratic form using the Schur complement.
  have h_decomp : ∀ v : Fin (n + 1) → ℝ, dotProduct v (mulVec M v) = dotProduct (v ∘ Fin.castSucc + v (Fin.last n) • (M.leadingSubmatrix n (Nat.le_succ n))⁻¹.mulVec (lastCol M)) (mulVec (M.leadingSubmatrix n (Nat.le_succ n)) (v ∘ Fin.castSucc + v (Fin.last n) • (M.leadingSubmatrix n (Nat.le_succ n))⁻¹.mulVec (lastCol M))) + schurComplement M * (v (Fin.last n))^2 := by
    exact?;
  refine' ⟨ hM, fun v hv => _ ⟩;
  by_cases h_last : v (Fin.last n) = 0;
  · have := hA.2;
    convert this ( show ( v.comapDomain ( Fin.castSucc ) fun i => by aesop ) ≠ 0 from ?_ ) using 1;
    · simp +decide [ Finsupp.sum_fintype, Fin.sum_univ_castSucc, h_last ];
      rfl;
    · contrapose! hv;
      ext i; by_cases hi : i = Fin.last n <;> simp_all +decide [ Finsupp.ext_iff ] ;
      convert hv ⟨ i.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hi ) ⟩;
  · -- Since $v (Fin.last n) \neq 0$, we have $schurComplement M * (v (Fin.last n))^2 > 0$.
    have h_schur_pos : 0 < schurComplement M * (v (Fin.last n))^2 := by
      exact mul_pos ( schur_complement_pos M hM hA hdet ) ( by positivity );
    convert add_pos_of_nonneg_of_pos ( posDef_dotProduct_nonneg _ hA _ ) h_schur_pos using 1;
    convert h_decomp ( fun i => v i ) using 1;
    simp +decide [ Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ]
