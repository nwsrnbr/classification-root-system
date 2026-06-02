import Mathlib.Data.Matrix.Cartan
import RootSystem.SylvesterCriterion.SylvesterForward
import RootSystem.Cartan.Auxiliary

namespace CartanMatrix

open Matrix

variable {n : ℕ} {k : ℕ} {hk : k ≤ n}

lemma A_leadingSubmatrix : (A n).leadingSubmatrix k hk =
    A k := by
  ext i j
  simp [A, of_apply, leadingSubmatrix]
  grind

lemma B_leadingSubmatrix : (B n).leadingSubmatrix k hk =
    if k = n then B k
    else A k := by
  by_cases h : k = n
  repeat'
    simp only [h]
    ext i j
    simp [A, B, of_apply, leadingSubmatrix]
    grind

lemma C_leadingSubmatrix : (C n).leadingSubmatrix k hk =
    if k = n then C k
    else A k := by
  by_cases h : k = n
  repeat'
    simp only [h]
    ext i j
    simp [A, C, of_apply, leadingSubmatrix]
    grind

lemma D_leadingSubmatrix : (D n).leadingSubmatrix k hk =
    if k = n then D k
    else A k := by
  by_cases h : k = n
  repeat'
    simp only [h]
    ext i j
    simp [A, D, of_apply, leadingSubmatrix]
    grind

lemma D_rev_leadingSubmatrix : (D_rev n).leadingSubmatrix k hk =
    D_rev k := by
  ext i j
  simp [D_rev, of_apply, leadingSubmatrix]
  grind

lemma E_leadingSubmatrix (hn : n ≤ 8) : (E n).leadingSubmatrix k hk =
    E k := by
  interval_cases n
  <;> interval_cases k
  <;> simp only [leadingSubmatrix]
  <;> revert hk
  <;> decide

lemma F₄_leadingSubmatrix (hk : k ≤ 4) : F₄.leadingSubmatrix k hk =
    if h4 : k = 4 then F₄.reindex (finCongr h4.symm) (finCongr h4.symm)
    else if k = 3 then B k
    else A k := by
  interval_cases k
  repeat'
    ext i j
    fin_cases i
    <;> fin_cases j
    <;> simp [F₄, of_apply, leadingSubmatrix, A, B]



variable {n : ℕ} {R : Type*} [CommRing R]

/-- The principal matrix of order n of `Y`. -/
def isTopLeftBlock (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
  Y.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

omit [CommRing R] in
lemma isTopLeftBlock_eq (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    isTopLeftBlock Y = Y.leadingSubmatrix n (by linarith) := by
  simp only [isTopLeftBlock, leadingSubmatrix]
  rw [Fin.castSucc, Fin.castAdd]

lemma A_isTopLeftBlock : isTopLeftBlock (A (n + 1)) = A n := by
  rw [isTopLeftBlock_eq, A_leadingSubmatrix]

lemma B_isTopLeftBlock : isTopLeftBlock (B (n + 1)) = A n := by
  simp [isTopLeftBlock_eq, B_leadingSubmatrix]

lemma D_rev_isTopLeftBlock : isTopLeftBlock (D_rev (n + 1)) = D_rev n := by
  rw [isTopLeftBlock_eq, D_rev_leadingSubmatrix]

lemma E_isTopLeftBlock (hn : n ≤ 7) : isTopLeftBlock (E (n + 1)) = E n := by
  rw [isTopLeftBlock_eq, E_leadingSubmatrix (by linarith)]

lemma F₄_isTopLeftBlock : isTopLeftBlock F₄ = B 3 := by
  simp [isTopLeftBlock_eq, F₄_leadingSubmatrix]

end CartanMatrix
