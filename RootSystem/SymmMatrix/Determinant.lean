import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import RootSystem.Cartan.Determinant
import Mathlib.Data.Matrix.Cartan
import Mathlib.Tactic.FinCases

--set_option maxHeartbeats 1000000

universe u

namespace CartanMatrix

variable {n : ℕ}

open Matrix

section Preliminaries

variable {n : ℕ}

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

lemma SymmMatrix_trans_rfl (C : Matrix (Fin n) (Fin n) ℤ) : (SymmMatrix C).IsSymm := by
  ext i j
  simp [SymmMatrix, mul_comm]
  aesop

lemma det_SymmMatrix_eq (C : Matrix (Fin n) (Fin n) ℤ) (hs : C.IsSymm)
    (hd : ∀ i, C i i = 2) (hn : ∀ i j, ¬i = j → C i j ≤ 0) :
    (SymmMatrix C).det = C.det := by
  rw [Int.cast_det]
  congr
  ext i j
  dsimp [SymmMatrix]
  split_ifs with h'
  · rw [h', hd]
    simp
  · rw [IsSymm.apply hs i j, Real.sqrt_mul_self_eq_abs, abs_of_nonpos (by simp [h', hn])]
    simp

end Preliminaries

variable (n : ℕ)

theorem det_SymmMatrix_A : (SymmMatrix (A n)).det = (n : ℝ) + 1 := by
  rw [det_SymmMatrix_eq (A n) (A_isSymm n) (by simp [A, Matrix.of_apply]) (A_apply_le_zero_of_ne n)]
  simp [det_A]

theorem det_SymmMatrix_B : (SymmMatrix (B n)).det = if n = 0 then 1 else 2 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [SymmMatrix]
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det (SymmMatrix (B (n + 1 + 1))) (SymmMatrix (A (n + 1)))
          (SymmMatrix (A n)) (-√2) (-√2)]
      · simp [det_SymmMatrix_A]; ring
      · ext i j
        simp [SymmMatrix, ind_matrix, A, B, Fin.castLT]
        grind
      · simp [isTopLeftBlock, SymmMatrix, A]
        aesop


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
  rw [det_SymmMatrix_eq (D n) (D_isSymm n) (D_diag n) (D_off_diag_nonpos n)]
  simp [det_D]


theorem det_SymmMatrix_E₆ : (SymmMatrix E₆).det = 3 := by
  rw [det_SymmMatrix_eq E₆ (E₆_isSymm) (E₆_diag) (E₆_off_diag_nonpos)]
  simp [det_E₆]

theorem det_SymmMatrix_E₇ : (SymmMatrix E₇).det = 2 := by
  rw [det_SymmMatrix_eq E₇ (E₇_isSymm) (E₇_diag) (E₇_off_diag_nonpos)]
  simp [det_E₇]

theorem det_SymmMatrix_E₈ : (SymmMatrix E₈).det = 1 := by
  rw [det_SymmMatrix_eq E₈ (E₈_isSymm) (E₈_diag) (E₈_off_diag_nonpos)]
  simp [det_E₈]

theorem det_SymmMatrix_F₄ : (SymmMatrix F₄).det = 1 := by
  rw [ind_det (SymmMatrix F₄) (SymmMatrix (B (2 + 1))) (SymmMatrix (A 2)) (-1 : ℝ) (-1 : ℝ)]
  · simp [det_SymmMatrix_A, det_SymmMatrix_B]
    norm_num
  · ext i j
    simp only [SymmMatrix, ind_matrix, F₄, B, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, SymmMatrix, B, A]
    fin_cases i
    <;> fin_cases j
    <;> simp

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
