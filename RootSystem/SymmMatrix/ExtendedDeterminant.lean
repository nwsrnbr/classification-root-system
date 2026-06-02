import Mathlib.Tactic
import RootSystem.Cartan.ExtendedDeterminant
import RootSystem.SymmMatrix.Determinant
import Mathlib.Data.Matrix.Cartan
import Mathlib.Tactic.FinCases

--set_option maxHeartbeats 500000

namespace CartanMatrix

variable {n : ℕ}

open Matrix

section Preliminaries

variable (n : ℕ)

theorem det_SymmMatrix_C_rev : (SymmMatrix (rev (C n))).det = (SymmMatrix (C n)).det := by
  have : (SymmMatrix (rev (C n))) = rev (SymmMatrix (C n)) := by
    ext i j
    simp [SymmMatrix, rev]
  rw [this, det_rev]

theorem det_SymmMatrix_D_rev : (SymmMatrix (D_rev n)).det = (SymmMatrix (D n)).det := by
  rw [det_SymmMatrix_eq_rfl (D_isSymm n) (D_diag n) (isSimplyLaced_D n)]
  rw [D_rev_eq, det_SymmMatrix_eq_rfl (rev_isSymm (D_isSymm n)) (by simp [rev_diag, D_diag])
      (isSimplyLaced_rev (isSimplyLaced_D n))]
  · rw [det_rev]

end Preliminaries

variable (n : ℕ)

theorem det_SymmMatrix_A_tilda : (SymmMatrix (A_tilda n)).det =
    if n = 0 then 2
    else if n = 1 then 3
    else 0 := by
  rw [det_SymmMatrix_eq_rfl (A_tilda_isSymm n) (A_tilda_diag n) (isSimplyLaced_A_tilda n)]
  simp [det_A_tilda]

theorem det_SymmMatrix_B_tilda : (SymmMatrix (B_tilda n)).det =
    if n = 0 ∨ n = 1 then 2
    else if n = 2 then 4
    else 0 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp [SymmMatrix]
  | succ n =>
    cases n with
    | zero =>
      have : SymmMatrix (B_tilda 1) = !![2, -√2; -√2, 2] := by
        simp only [SymmMatrix, B_tilda]
        ext i j
        fin_cases i
        <;> fin_cases j
        <;> simp
      simp [this]; norm_num
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      by_cases hn : n = 0
      · rw [hn]
        have : SymmMatrix (B_tilda 2) = !![2, 0, 0; 0, 2, -√2; 0, -√2, 2] := by
          dsimp [SymmMatrix, B_tilda, D_rev]
          ext i j
          fin_cases i
          <;> fin_cases j
          <;> simp
        simp [this, Matrix.det_fin_three]
        grind
      · rw [ind_det (SymmMatrix (B_tilda (n + 1 + 1))) (SymmMatrix (D_rev (n + 1 + 1)))
            (SymmMatrix (D_rev (n + 1))) (-√2 : ℝ) (-√2 : ℝ)]
        · simp [det_SymmMatrix_D_rev, det_SymmMatrix_D]
          aesop
        · ext i j
          simp [SymmMatrix, ind_matrix, B_tilda, Fin.castLT]
          by_cases hi : i ≤ n + 1
          by_cases hj : j ≤ n + 1
          · simp [hi, hj]
            grind
          · have : j = n + 1 + 1 := by omega
            simp [hi, hj]
            split_ifs
            <;> grind
          · simp [hi]
            have : i = n + 1 + 1 := by omega
            split_ifs
            <;> grind
        · rw [SymmMatrix_D_rev_isTopLeftBlock]

theorem det_SymmMatrix_C_tilda : (SymmMatrix (C_tilda n)).det =
    if n = 0 ∨ n = 1 then 2
    else 0 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp [SymmMatrix, C_tilda]
  | succ n =>
    cases n with
    | zero =>
      have : SymmMatrix (C_tilda 1) = !![2, -√2; -√2, 2] := by
        simp only [SymmMatrix, C_tilda]
        ext i j
        fin_cases i
        <;> fin_cases j
        <;> simp
      simp [this]; norm_num
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det (SymmMatrix (C_tilda (n + 1 + 1))) (SymmMatrix (rev (C (n + 1 + 1))))
          (SymmMatrix (rev (C (n + 1)))) (-√2) (-√2)]
      · simp [det_SymmMatrix_C_rev, det_SymmMatrix_C]
      · ext i j
        simp [SymmMatrix, ind_matrix, C_tilda, Fin.castLT]
        by_cases hi : i ≤ n + 1
        by_cases hj : j ≤ n + 1
        · simp [hi, hj]
          grind
        · have : j = n + 1 + 1 := by omega
          simp [hi, hj]
          split_ifs
          <;> grind
        · simp [hi]
          have : i = n + 1 + 1 := by omega
          split_ifs
          <;> grind
      · ext i j
        simp [isTopLeftBlock, SymmMatrix, rev, C]
        grind

theorem det_SymmMatrix_D_tilda (n : ℕ) : (SymmMatrix (D_tilda n)).det =
    if n = 0 then 2
    else if n = 1 then 3
    else if n = 2 ∨ n = 3 then 4
    else if n = 4 then 8
    else 0 := by
  rw [det_SymmMatrix_eq_rfl (D_tilda_isSymm n) (D_tilda_diag n) (isSimplyLaced_D_tilda n)]
  simp [det_D_tilda]

theorem det_SymmMatrix_E_tilda₆ : (SymmMatrix E_tilda₆).det = 0 := by
  rw [det_SymmMatrix_eq_rfl E_tilda₆_isSymm E_tilda₆_diag isSimplyLaced_E_tilda₆]
  simp [det_E_tilda₆]

theorem det_SymmMatrix_E_tilda₇ : (SymmMatrix E_tilda₇).det = 0 := by
  rw [det_SymmMatrix_eq_rfl E_tilda₇_isSymm E_tilda₇_diag isSimplyLaced_E_tilda₇]
  simp [det_E_tilda₇]

theorem det_SymmMatrix_E_tilda₈ : (SymmMatrix E_tilda₈).det = 0 := by
  rw [det_SymmMatrix_eq_rfl E_tilda₈_isSymm E_tilda₈_diag isSimplyLaced_E_tilda₈]
  simp [det_E_tilda₈]

theorem det_SymmMatrix_F_tilda₄ : (SymmMatrix F_tilda₄).det = 0 := by
  rw [ind_det (SymmMatrix F_tilda₄) (SymmMatrix F₄) (SymmMatrix (B 3)) (-1) (-1)]
  · simp [det_SymmMatrix_F₄, det_SymmMatrix_B]
  · ext i j
    simp only [SymmMatrix, ind_matrix, F_tilda₄, F₄, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · rw [SymmMatrix_F₄_isTopLeftBlock]

theorem det_SymmMatrix_G_tilda₂ : (SymmMatrix G_tilda₂).det = 0 := by
  have : SymmMatrix G_tilda₂ = !![2, -√3, 0; -√3, 2, -1; 0, -1, 2] := by
    simp only [G_tilda₂, SymmMatrix]
    ext i j
    fin_cases i
    <;> fin_cases j
    <;> simp
  simp [this, det_fin_three]
  norm_num

end CartanMatrix
