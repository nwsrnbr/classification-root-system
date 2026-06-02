import RootSystem.SymmMatrix.Basic

namespace CartanMatrix

open Matrix

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

end CartanMatrix
