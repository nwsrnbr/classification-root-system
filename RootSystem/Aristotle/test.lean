import Mathlib.Tactic
import Mathlib.Data.Matrix.Cartan

namespace CartanMatrix

open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The matrix obtained by adding a row and a column to `Y`, with entries `a` and `b`,
where `a` and `b` are the (n-1, n)- and (n, n-1)-entries, respectively.
The (n, n)-entry is `2`, and all other entries in the n-th row and n-th column are `0`. -/
def ind_matrix (Y : Matrix (Fin n) (Fin n) R) (a b : R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then Y (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i then a
    else if (i : ℕ) + 1 = j then b
    else 0

/-- The principal matrix of order n of `Y`. -/
def isTopLeftBlock (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
  Y.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

/-- The recurrence relation for the determinant satisfying the specified property. -/
-- This has already been proven in another file, so you do not need to prove it here.
lemma ind_det (X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) R)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (Z : Matrix (Fin n) (Fin n) R)
    (a b : R)
    (hX : X = ind_matrix Y a b)
    (hY : isTopLeftBlock Y = Z) :
  X.det = 2 * Y.det - a * b * Z.det := by
    sorry

-- This has already been proven in another file, so you do not need to prove it here.
theorem det_D (n : ℕ) : det (D n) =
  if n = 0 then 1
  else if n = 1 then 2
  else 4 := by
    sorry

def D_rev (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

-- This has already been proven in another file, so you do not need to prove it here.
theorem det_D_rev (n : ℕ) : (D_rev n).det = (D n).det := by
  sorry


/-- The Cartan matrix of type \widetilde{D}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o                       o
     \                     /
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /                     \
    o                       o
```
-/
def D_tilda (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n - 2 ∧ j < n - 2 then (D_rev n) (i.castLT (by omega)) (j.castLT (by omega))
    else if i = j then 2
    else if i.val + 1 = n ∧ (j.val + 3 = n ∨ j.val + 2 = n ∨ j.val = n) then -1
    else if j.val + 1 = n ∧ (i.val + 3 = n ∨ i.val + 2 = n ∨ i.val = n) then -1
    else 0

def D_tilda_remove_last (n : ℕ) (h : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  let e := Equiv.swap ⟨n-2, by omega⟩ ⟨n-1, by omega⟩
  (reindex e e) (D_rev n)

lemma det_D_tilda_remove_last (n : ℕ) (h : 2 ≤ n) : (D_tilda_remove_last n h).det = (D n).det := by
  simp [D_tilda_remove_last, det_D_rev]

def D_tilda_remove_last_two (n : ℕ) :=
  Matrix.fromBlocks
    (D_rev (n-1))
    (0 : Matrix (Fin (n-1)) (Fin 1) ℤ)
    (0 : Matrix (Fin 1) (Fin (n-1)) ℤ)
    (fun _ _ => (2 : ℤ))

lemma det_D_tilda_remove_last_two (n : ℕ) :
    (D_tilda_remove_last_two n).det = (D (n - 1)).det * 2 := by
  simp [D_tilda_remove_last_two, det_D_rev]

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
