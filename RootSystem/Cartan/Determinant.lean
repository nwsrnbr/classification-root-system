/-
Copyright (c) 2026 Noboru Nawashiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noboru Nawashiro, Daisuke Matsushita
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Matrix.Cartan

/-!
# Cartan matrices

This file computes determinants of Cartan matrices for simple Lie algebras, both the exceptional
types (E₆, E₇, E₈, F₄, G₂) and the classical infinite families (A, B, C, D).

## Main results

### Exceptional types
* `CartanMatrix.det_E₆` : The determinant of the Cartan matrix of type E₆
* `CartanMatrix.det_E₇` : The determinant of the Cartan matrix of type E₇
* `CartanMatrix.det_E₈` : The determinant of the Cartan matrix of type E₈
* `CartanMatrix.det_F₄` : The determinant of the Cartan matrix of type F₄
* `CartanMatrix.det_G₂` : The determinant of the Cartan matrix of type G₂

### Classical types
* `CartanMatrix.det_A` : The determinant of the Cartan matrix of type Aₙ₋₁ (corresponding to sl(n))
* `CartanMatrix.det_B` : The determinant of the Cartan matrix of type Bₙ (corresponding to so(2n+1))
* `CartanMatrix.det_C` : The determinant of the Cartan matrix of type Cₙ (corresponding to sp(2n))
* `CartanMatrix.det_D` : The determinant of the Cartan matrix of type Dₙ (corresponding to so(2n))

## References

* [J. Humphreys, *Reflection groups and Coxeter groups*]

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

@[expose] public section

namespace CartanMatrix

open Matrix

section Preliminaries

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
lemma ind_det (X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) R)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (Z : Matrix (Fin n) (Fin n) R)
    (a b : R)
    (hX : X = ind_matrix Y a b)
    (hY : isTopLeftBlock Y = Z) :
  X.det = 2 * Y.det - a * b * Z.det := by
    have h_col : ∀ (j : Fin n), ind_matrix Y a b (Fin.last (n + 1)) j.castSucc.castSucc = 0 := by
      intro j
      dsimp [ind_matrix]
      grind
    have h_row : ∀ (i : Fin n), ind_matrix Y a b i.castSucc.castSucc (Fin.last (n + 1)) = 0 := by
      intro i
      simp [ind_matrix]
      grind
    rw [X.det_succ_row (Fin.last (n + 1)), hX]
    rw [Fin.sum_univ_succAbove (x := Fin.last (n + 1)), Fin.sum_univ_succAbove (x := Fin.last n)]
    norm_num
    simp only [h_col]
    have (x y z w : R) : x = z ∧ y = -w → x + y = z - w := by intros; simp [*]; ring
    apply this
    split_ands
    · simp only [ind_matrix, Fin.castLT]
      norm_num
      congr 1
      congr 1
      ext i j
      simp
      omega
    · rw [det_succ_column (j := Fin.last n), Fin.sum_univ_succAbove (x := Fin.last n)]
      norm_num
      simp only [h_row]
      norm_num
      rw [← mul_assoc]
      congr 1
      · --rw [pow_two]
        congr
        · simp [ind_matrix, Fin.last]
        · simp [ind_matrix]
          omega
      · dsimp [ind_matrix, Fin.castLT]
        congr 1
        ext i j
        simp
        simp [← hY, isTopLeftBlock]
        congr

/-- The principal submatrix of order 3 of E₆. -/
def E₃ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 2,  0, -1;
      0,  2,  0;
     -1,  0,  2;]

/-- The principal submatrix of order 4 of E₆. -/
def E₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2,  0, -1,  0;
      0,  2,  0, -1;
     -1,  0,  2, -1;
      0, -1, -1,  2]

/-- The principal submatrix of order 5 of E₆. -/
def E₅ : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 2,  0, -1,  0,  0;
      0,  2,  0, -1,  0;
     -1,  0,  2, -1,  0;
      0, -1, -1,  2, -1;
      0,  0,  0, -1,  2]

lemma det_E₃ : E₃.det = 6 := by decide

lemma det_E₄ : E₄.det = 5 := by decide

lemma det_E₅ : E₅.det = 4 := by
  rw [ind_det E₅ E₄ E₃ (-1) (-1)]
  · simp [det_E₄, det_E₃]
  · ext i j
    simp only [ind_matrix, E₅, E₄, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, E₄, E₃]
    fin_cases i
    <;> fin_cases j
    <;> simp

def rev (X : Matrix (Fin n) (Fin n) R) := Matrix.of fun i j : Fin n ↦ X (i.rev) (j.rev)

lemma det_rev (X : Matrix (Fin n) (Fin n) R) : (rev X).det = X.det := by
  let e := Equiv.ofBijective (fun i : Fin n ↦ i.rev) Fin.rev_bijective
  have : rev X = (reindex e e) X := by
    ext i j
    simp [rev, reindex, e, Equiv.ofBijective, Function.surjInv]
    grind
  simp [this]

omit [CommRing R]
lemma rev_isSymm {X : Matrix (Fin n) (Fin n) R} (h : X.IsSymm) : (rev X).IsSymm := by
  ext i j
  dsimp [rev]
  rw [IsSymm.apply h]

def D_rev (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

lemma D_rev_eq (n : ℕ) : D_rev n = rev (D n) := by
  ext i j
  simp [D_rev, rev, D, Fin.rev]
  split_ifs
  <;> grind

end Preliminaries

/-! ### Classical Cartan matrices -/

/-- The determinant of Aₙ. -/
theorem det_A (n : ℕ) : det (A n) = n + 1 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [A_one]
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det (A (n + 1 + 1)) (A (n + 1)) (A n) (-1) (-1)]
      · simp [h1, h2]; ring
      · ext i j
        simp [ind_matrix, A, Fin.castLT]
        grind
      · ext i j
        simp [isTopLeftBlock, A]
        omega

/-- The determinant of Bₙ. -/
theorem det_B (n : ℕ) : det (B n) = if n = 0 then 1 else 2 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det (B (n + 1 + 1)) (A (n + 1)) (A n) (-1) (-2)]
      · simp [det_A]; ring
      · ext i j
        simp [ind_matrix, A, B, Fin.castLT]
        grind
      · ext i j
        simp [isTopLeftBlock, A]
        omega

/-- The determinant of Cₙ. -/
theorem det_C (n : ℕ) : det (C n) = if n = 0 then 1 else 2 := by
  rw [← det_transpose, C_transpose, det_B]

/-- The determinant of Dₙ. -/
theorem det_D (n : ℕ) : det (D n) =
  if n = 0 then 1
  else if n = 1 then 2
  else 4 :=
    Nat.strong_induction_on n fun n ih => by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      by_cases hn : n = 0
      · rw [hn]
        decide
      by_cases hn' : n = 1
      · rw [hn']
        decide
      · have : ¬n < 2 := by omega
        rw [← det_rev, ← D_rev_eq]
        rw [ind_det (D_rev (n + 1 + 1)) (D_rev (n + 1)) (D_rev n) (-1) (-1)]
        · simp [D_rev_eq, det_rev, h1, h2]
          split_ifs
          norm_num
        · ext i j
          simp [ind_matrix, D_rev, Fin.castLT]
          grind
        · ext i j
          simp [isTopLeftBlock, D_rev, Fin.castSucc, Fin.castAdd, Fin.castLE]
          grind

/-! ### Exceptional Cartan matrices -/

/-- The determinant of E₆. -/
theorem det_E₆ : det E₆ = 3 := by
  rw [ind_det E₆ E₅ E₄ (-1) (-1)]
  · simp [det_E₅, det_E₄]
  · ext i j
    simp only [ind_matrix, E₆, E₅, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, E₅, E₄]
    fin_cases i
    <;> fin_cases j
    <;> simp

/-- The determinant of E₇. -/
theorem det_E₇ : det E₇ = 2 := by
  rw [ind_det E₇ E₆ E₅ (-1) (-1)]
  · simp [det_E₆, det_E₅]
  · ext i j
    simp only [ind_matrix, E₇, E₆, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, E₆, E₅]
    fin_cases i
    <;> fin_cases j
    <;> simp

/-- The determinant of E₈. -/
theorem det_E₈ : det E₈ = 1 := by
  rw [ind_det E₈ E₇ E₆ (-1) (-1)]
  · simp [det_E₇, det_E₆]
  · ext i j
    simp only [ind_matrix, E₈, E₇, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp only [isTopLeftBlock, E₇, E₆]
    fin_cases i
    <;> fin_cases j
    <;> simp

/-- The determinant of F₄. -/
theorem det_F₄ : det F₄ = 1 := by
  decide

/-- The determinant of G₂. -/
theorem det_G₂ : det G₂ = 1 := by
  decide

end CartanMatrix

end
