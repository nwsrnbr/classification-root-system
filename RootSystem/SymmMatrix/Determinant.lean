import Mathlib.Tactic
import Mathlib.Data.Matrix.Cartan
import Mathlib.Tactic.FinCases
import RootSystem.Cartan.Determinant
import RootSystem.SymmMatrix.Basic

namespace CartanMatrix

variable {n : ℕ}

open Matrix

variable (n : ℕ)

theorem det_SymmMatrix_A : (SymmMatrix (A n)).det = (n : ℝ) + 1 := by
  rw [det_SymmMatrix_eq_rfl (A_isSymm n) (by simp [A, Matrix.of_apply]) (isSimplyLaced_A n)]
  simp [det_A]

theorem det_SymmMatrix_B : (SymmMatrix (B n)).det = if n = 0 then 1 else 2 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [SymmMatrix]
    | succ n =>
      rw [ind_det (SymmMatrix (B (n + 1 + 1))) (SymmMatrix (A (n + 1)))
          (SymmMatrix (A n)) (-√2) (-√2)]
      · simp [det_SymmMatrix_A]; ring
      · ext i j
        simp [SymmMatrix, ind_matrix, A, B, Fin.castLT]
        grind
      · rw [SymmMatrix_A_isTopLeftBlock]

theorem det_SymmMatrix_C : (SymmMatrix (C n)).det = if n = 0 then 1 else 2 := by
  calc
    _ = (SymmMatrix (B n).transpose).det := by rw [B_transpose]
    _ = (SymmMatrix (B n)).det := by
      congr 1
      simp [SymmMatrix]
      grind
    _ = if n = 0 then 1 else 2 := by rw [det_SymmMatrix_B]

theorem det_SymmMatrix_D : (SymmMatrix (D n)).det =
    if n = 0 then 1
    else if n = 1 then 2
    else 4 := by
  rw [det_SymmMatrix_eq_rfl (D_isSymm n) (D_diag n) (isSimplyLaced_D n)]
  simp [det_D]

theorem det_SymmMatrix_E (hn : n ≤ 8) : (SymmMatrix (E n)).det =
    if n = 0 then 1
    else if n = 1 then 2
    else if n = 2 then 4
    else 9 - n := by
  by_cases h : n = 0
  · rw [h]; simp
  · rw [det_SymmMatrix_eq_rfl (E_isSymm hn) (by intro; simp [E_diag _ h hn]) (isSimplyLaced_E n hn)]
    interval_cases n
    · simp
    · simp
    · simp [E]
    · simp [det_E₃]
    · simp [det_E₄]
    · simp [det_E₅]
    · simp [E, det_E₆]
    · simp [E, det_E₇]
    · simp [E, det_E₈]

theorem det_SymmMatrix_E₆ : (SymmMatrix E₆).det = 3 := by
  rw [← E, det_SymmMatrix_E 6 (by norm_num)]; simp

theorem det_SymmMatrix_E₇ : (SymmMatrix E₇).det = 2 := by
  rw [← E, det_SymmMatrix_E 7 (by norm_num)]; simp

theorem det_SymmMatrix_E₈ : (SymmMatrix E₈).det = 1 := by
  rw [← E, det_SymmMatrix_E 8 (by norm_num)]; simp

theorem det_SymmMatrix_F₄ : (SymmMatrix F₄).det = 1 := by
  rw [ind_det (SymmMatrix F₄) (SymmMatrix (B (2 + 1))) (SymmMatrix (A 2)) (-1 : ℝ) (-1 : ℝ)]
  · simp [det_SymmMatrix_A, det_SymmMatrix_B]
    norm_num
  · ext i j
    simp only [SymmMatrix, ind_matrix, F₄, B, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · rw [SymmMatrix_B_isTopLeftBlock]

theorem det_SymmMatrix_G₂ : (SymmMatrix G₂).det = 1 := by
  have : SymmMatrix G₂ = !![2, -√3; -√3, 2] := by
    simp only [G₂, SymmMatrix]
    ext i j
    fin_cases i
    <;> fin_cases j
    <;> simp
  rw [this]
  simp; norm_num

section Extended



end Extended

end CartanMatrix
