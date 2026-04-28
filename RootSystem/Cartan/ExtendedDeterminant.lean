import Mathlib.Tactic
import Mathlib.Data.Matrix.Cartan
import RootSystem.Cartan.Determinant
import RootSystem.Cartan.ExtendedCartan

namespace CartanMatrix

open Matrix

section Preliminaries

def D_tilda_remove_last (n : ℕ) (h : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  let e := Equiv.swap ⟨n-2, by omega⟩ ⟨n-1, by omega⟩
  (reindex e e) (D_rev n)

lemma det_D_tilda_remove_last (n : ℕ) (h : 2 ≤ n) : (D_tilda_remove_last n h).det = (D n).det := by
  simp [D_tilda_remove_last, D_rev_eq, det_rev]

def D_tilda_remove_last_two (n : ℕ) :=
  Matrix.fromBlocks
    (D_rev (n-1))
    (0 : Matrix (Fin (n-1)) (Fin 1) ℤ)
    (0 : Matrix (Fin 1) (Fin (n-1)) ℤ)
    (fun _ _ => (2 : ℤ))

lemma det_D_tilda_remove_last_two (n : ℕ) :
    (D_tilda_remove_last_two n).det = (D (n - 1)).det * 2 := by
  simp [D_tilda_remove_last_two, D_rev_eq, det_rev]

/-- The principal submatrix of order 6 of \widetilde{E}₆. -/
def E_tilda₅ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, -1, 0, 0, 0, 0;
    -1, 2, 0, 0, -1, 0;
    0, 0, 2, -1, 0, 0;
    0, 0, -1, 2, -1, 0;
    0, -1, 0, -1, 2, -1;
    0, 0, 0, 0, -1, 2]

def E_tilda₄ : Matrix (Fin 5) (Fin 5) ℤ :=
  (A 5).reindex c[2, 4] c[2, 4]

def E_tilda₃ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0;
    -1, 2, 0, 0;
    0, 0, 2, -1;
    0, 0, -1, 2]

lemma det_E_tilda₃ : E_tilda₃.det = 9 := by decide

lemma det_E_tilda₄ : E_tilda₄.det = 6 := by
  simp [E_tilda₄, det_A]

lemma det_E_tilda₅ : E_tilda₅.det = 3 := by
  rw [ind_det E_tilda₅ E_tilda₄ E_tilda₃ (-1) (-1)]
  · simp [det_E_tilda₄, det_E_tilda₃]
  · ext i j
    simp only [ind_matrix, E_tilda₅, E_tilda₄, A, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> decide
  · ext i j
    simp only [isTopLeftBlock, E_tilda₄, E_tilda₃, A]
    fin_cases i
    <;> fin_cases j
    <;> decide


end Preliminaries

theorem det_D_tilda (n : ℕ) : (D_tilda n).det =
  if n = 0 then 2
  else if n = 1 then 3
  else if n = 2 ∨ n = 3 then 4
  else if n = 4 then 8
  else 0 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      by_cases hn0 : n = 0
      · rw [hn0]
        decide
      by_cases hn1 : n = 1
      · rw [hn1]
        decide
      by_cases hn2 : n = 2
      · rw [hn2]
        have : D_tilda 4 =
            (Matrix.fromBlocks
              (fun _ _ => (2 : ℤ))
              (0 : Matrix (Fin 1) (Fin 4) ℤ)
              (0 : Matrix (Fin 4) (Fin 1) ℤ)
              (D_rev 4)).reindex
              (finSumFinEquiv (m := 1) (n := 4)) (finSumFinEquiv (m := 1) (n := 4)) := by
          ext i j
          fin_cases i
          <;> fin_cases j
          <;> decide
        simp [this, D_rev_eq, det_rev, det_D]
      · rw [ind_det (D_tilda (n + 1 + 1)) (D_tilda_remove_last (n + 1 + 1) (by omega))
            ((D_tilda_remove_last_two (n + 1)).reindex
              (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)))
            (-1) (-1)]
        · simp [det_D_tilda_remove_last]
          change 2 * (D (n + 1 + 1)).det - (D_tilda_remove_last_two (n + 1)).det = _
          rw [det_D_tilda_remove_last_two (n + 1)]
          simp only [det_D]
          omega
        · ext i j
          simp [D_tilda, ind_matrix, D_tilda_remove_last, Equiv.swap_apply_def, Fin.castLT]
          by_cases hi : i < n
          have hi' : i ≤ n + 1 := by omega
          by_cases hj : j < n
          · have hj' : j ≤ n + 1 := by omega
            simp [hi, hj, hi', hj']
            grind
          · have hj' : j = n ∨ j = n + 1 ∨ j = n + 2 := by omega
            rcases hj' with (hj' | hj' | hj')
            <;> simp [hi, hi', hj', D_rev]
            <;> grind
          · have hi' : i = n ∨ i = n + 1 ∨ i = n + 2 := by omega
            rcases hi' with (hi' | hi' | hi')
            <;> simp [hi', D_rev]
            <;> grind
        · ext i j
          simp [isTopLeftBlock, D_tilda_remove_last, D_tilda_remove_last_two]
          simp [Equiv.swap_apply_def, finSumFinEquiv]
          simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.addCases, Fin.castLT]
          rcases i with ⟨i, hi⟩
          rcases j with ⟨j, hj⟩
          have hni1 : ¬i = n + 1 := by omega
          have hni2 : ¬n + 1 + 1 = i := by omega
          have hnj1 : ¬j = n + 1 := by omega
          have hnj2 : ¬n + 1 + 1 = j := by omega
          by_cases hi : i < n
          <;> by_cases hj : j < n
          · have hni0 : ¬i = n := by omega
            have hnj0 : ¬j = n := by omega
            simp [hi, hj, hni0, hni1, hnj0, hnj1, D_rev]
          · have hni0 : ¬i = n := by omega
            have hnj0 : j = n := by omega
            simp [hi, hni0, hni1, hnj0, D_rev]
            simp [hn0, hn1, hni2]
            rfl
          · have hni0 : i = n := by omega
            have hnj0 : ¬j = n := by omega
            have hnj1' : ¬n + 1 = j := by omega
            simp [hj, hni0, hnj1, hnj0, D_rev]
            simp [hn0, hn1, hnj1', hnj2]
            rfl
          · have hni0 : i = n := by omega
            have hnj0 : j = n := by omega
            simp [hni0, hnj0, D_rev]

theorem det_E_tilda₆ : (E_tilda₆).det = 0 := by
  rw [ind_det E_tilda₆ E_tilda₅ E_tilda₄ (-1) (-1)]
  · simp [det_E_tilda₅, det_E_tilda₄]
  · ext i j
    simp only [ind_matrix, E_tilda₆, E_tilda₅, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, E_tilda₅, E_tilda₄, A]
    fin_cases i
    <;> fin_cases j
    <;> decide

theorem det_E_tilda₇ : (E_tilda₇).det = 0 := by
  rw [ind_det E_tilda₇ (rev E₇) (D 6) (-1) (-1)]
  · simp [det_rev, det_E₇, det_D]
  · ext i j
    simp only [ind_matrix, E_tilda₇, rev, E₇, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, rev, E₇, D]
    fin_cases i
    <;> fin_cases j
    <;> simp

theorem det_E_tilda₈ : (E_tilda₈).det = 0 := by
  rw [ind_det E_tilda₈ E₈ E₇ (-1) (-1)]
  · simp [det_E₈, det_E₇]
  · ext i j
    simp only [ind_matrix, E_tilda₈, E₈, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, E₈, E₇]
    fin_cases i
    <;> fin_cases j
    <;> decide

theorem det_F_tilda₄ : (F_tilda₄).det = 0 := by
  rw [ind_det F_tilda₄ F₄ (B 3) (-1) (-1)]
  · simp [det_F₄, det_B]
  · ext i j
    simp only [ind_matrix, F_tilda₄, F₄, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, F₄, B]
    fin_cases i
    <;> fin_cases j
    <;> decide

theorem det_G_tilda₂ : (G_tilda₂).det = 0 := by decide

end CartanMatrix
