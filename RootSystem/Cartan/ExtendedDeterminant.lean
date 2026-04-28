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



/-
D_tilda 6 =
!![2, 0, -1, 0, 0, 0, 0;
  0, 2, -1, 0, 0, 0, 0;
  -1, -1, 2, -1, 0, 0, 0;
  0, 0, -1, 2, 0, -1, 0;
  0, 0, 0, 0, 2, -1, 0;
  0, 0, 0, -1, -1, 2, -1;
  0, 0, 0, 0, 0, -1, 2]

D_tilda 6 の左上 6 x 6 =
!![2, 0, -1, 0, 0, 0;
  0, 2, -1, 0, 0, 0;
  -1, -1, 2, -1, 0, 0;
  0, 0, -1, 2, 0, -1;
  0, 0, 0, 0, 2, -1;
  0, 0, 0, -1, -1, 2;]

D_tilda 6 の左上 5 x 5 =
!![2, 0, -1, 0, 0;
  0, 2, -1, 0, 0;
  -1, -1, 2, -1, 0;
  0, 0, -1, 2, 0;
  0, 0, 0, 0, 2]

-/

-- def D_tilda_remove_last_two (n : ℕ) (h : 1 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
--   ((Matrix.fromBlocks
--     (D_rev (n-1))
--     (0 : Matrix (Fin (n-1)) (Fin 1) ℤ)
--     (0 : Matrix (Fin 1) (Fin (n-1)) ℤ)
--     (fun _ _ => (2 : ℤ))).reindex
--       (finSumFinEquiv (m := n-1) (n := 1))
--       (finSumFinEquiv (m := n-1) (n := 1))).reindex
--         (by aesop)
--         (by aesop)


def D_tilda_remove_last_two (n : ℕ) :=
  Matrix.fromBlocks
    (D_rev (n-1))
    (0 : Matrix (Fin (n-1)) (Fin 1) ℤ)
    (0 : Matrix (Fin 1) (Fin (n-1)) ℤ)
    (fun _ _ => (2 : ℤ))

@[simp]
lemma det_D_tilda_remove_last_two (n : ℕ) :
    (D_tilda_remove_last_two n).det = (D (n - 1)).det * 2 := by
  simp [D_tilda_remove_last_two, D_rev_eq, det_rev]


def E_tilda₆' : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0;
    -1, 2, 0, 0, -1, 0, 0;
    0, 0, 2, -1, 0, 0, 0;
    0, 0, -1, 2, -1, 0, 0;
    0, -1, 0, -1, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, -1, 2]

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

#eval (D_tilda 4).det

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
      by_cases hn : n = 0
      · rw [hn]
        decide
      by_cases hn' : n = 1
      · rw [hn']
        decide
      · rw [ind_det (D_tilda (n + 1 + 1)) (D_tilda_remove_last (n + 1 + 1) (by omega))
            ((D_tilda_remove_last_two (n + 1)).reindex (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)))
            (-1) (-1)]
        · sorry
        · sorry
        · sorry

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
