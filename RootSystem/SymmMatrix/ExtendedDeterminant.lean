import Mathlib.Tactic
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import RootSystem.Cartan.Determinant
import RootSystem.Cartan.ExtendedCartan
import RootSystem.SymmMatrix.Determinant
import Mathlib.Data.Matrix.Cartan
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Tactic.FinCases

--set_option maxHeartbeats 500000

variable {ι E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (Φ : RootPairing ι ℝ E F) [Φ.IsRootSystem] [Φ.IsReduced]

variable [Φ.IsCrystallographic]

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (P : RootPairing ι R M N) [P.IsCrystallographic] {b : P.Base}

universe u

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
  rw [det_SymmMatrix_eq (D n) (D_isSymm n) (D_diag n) (D_off_diag_nonpos n)]
  rw [D_rev_eq, det_SymmMatrix_eq]
  · rw [det_rev]
  · apply rev_isSymm (D_isSymm n)
  · intro _
    dsimp [rev]
    rw [D_diag]
  · intro _ _ _
    dsimp [rev]
    apply D_off_diag_nonpos
    simpa

end Preliminaries

variable (n : ℕ)

def a' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 2
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1
        else (if i = (0 : ℕ) ∧ j = n ∨ j = (0 : ℕ) ∧ i = n then -1 else 0))

theorem det_SymmMatrix_a' : (SymmMatrix (a' n)).det =
    if n = 0 then 2
    else if n = 1 then 3
    else 0 := by
  sorry
  /-
  by_cases h0 : n = 0
  · rw [h0]
    simp [SymmMatrix, a']
  by_cases h1 : n = 1
  · rw [h1]
    have : SymmMatrix (a' 1) = !![2, -1; -1, 2] := by
      simp [SymmMatrix, a']
      ext i j
      fin_cases i
      <;> fin_cases j
      <;> simp
    simp [this]; norm_num
  · simp [h0, h1]
    rw [det_SymmMatrix_eq]
    · simp
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      let v : Fin (n + 1) → ℤ := fun _ ↦ 1
      use v
      split_ands
      · apply ne_zero_of_eq_one rfl
      · ext i
        simp [mulVec_eq_sum, a', v, Fin.castLT]
        have h0' : ¬0 = n := by omega
        have hnpos := Nat.pos_of_ne_zero h0

        by_cases hi0 : i = n
        · simp [hi0, hnpos, h0']
          simp [Fin.sum_univ_castSucc, Fin.castSucc, Fin.castAdd, Fin.castLE]
          have hx : ∀ x : Fin n, ¬(x : ℕ) = n := by omega
          simp [hx]
          sorry
        by_cases hin : i = n
        · simp [hi0]
          simp [hin] at *
          simp [hnpos]
    · ext i j
      simp [a', A, Fin.castLT]
      grind
    · intro i
      simp [a', A]
    · intro i j hij
      simp [a', A, Fin.castLT, hij]
      grind
  -/







theorem det_SymmMatrix_B_tilda : (SymmMatrix (B_tilda n)).det =
    if n = 0 ∨ n = 1 then 2
    else if n = 2 then 4
    else 0 := by
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simp [SymmMatrix]
  | succ n =>
    cases n with
    | zero =>
      have : SymmMatrix (B_tilda 1) = !![2, -√2; -√2, 2] := by
        simp [SymmMatrix, B_tilda]
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
        · ext i j
          simp [isTopLeftBlock, SymmMatrix, D_rev]
          split_ifs
          <;> simp

#eval C_tilda 5
#eval ind_matrix ((rev (C (3 + 1 + 1)))) (-1) (-2)

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
        simp [SymmMatrix, C_tilda]
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
