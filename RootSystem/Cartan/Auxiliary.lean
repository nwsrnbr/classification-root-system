import Mathlib.Tactic
import Mathlib.Data.Matrix.Cartan

namespace CartanMatrix

open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The matrix obtained by replacing each index `i` with `n - i + 1`. -/
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

lemma rev_diag {X : Matrix (Fin n) (Fin n) R} {i : Fin n} : (rev X) i i = X i.rev i.rev := by
  dsimp [rev]

lemma isSimplyLaced_rev {X : Matrix (Fin n) (Fin n) ℤ} (hs : X.IsSimplyLaced) :
    (rev X).IsSimplyLaced := by
  intro i j h
  dsimp [rev]
  apply hs
  simpa

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

lemma D_rev_isSymm (n : ℕ) : (D_rev n).IsSymm := by
  rw [D_rev_eq]
  apply rev_isSymm
  apply D_isSymm

lemma D_rev_diag (n : ℕ) (i : Fin n) : (D_rev n) i i = 2 := by
  rw [D_rev_eq, rev_diag, D_diag]

lemma D_rev_isSimplyLaced (n : ℕ) : (D_rev n).IsSimplyLaced := by
  rw [D_rev_eq]
  apply isSimplyLaced_rev
  apply isSimplyLaced_D

/-- The principal submatrix of order n of E₈. -/
def E : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ
  | 0 => !![]
  | 1 => !![2]
  | 2 => !![2, 0; 0, 2]
  | 3 => !![ 2,  0, -1;
             0,  2,  0;
            -1,  0,  2;]
  | 4 => !![ 2,  0, -1,  0;
             0,  2,  0, -1;
            -1,  0,  2, -1;
             0, -1, -1,  2]
  | 5 => !![ 2,  0, -1,  0,  0;
             0,  2,  0, -1,  0;
            -1,  0,  2, -1,  0;
             0, -1, -1,  2, -1;
             0,  0,  0, -1,  2]
  | 6 => E₆
  | 7 => E₇
  | 8 => E₈
  | _ => 0

@[simp] theorem E_diag (i : Fin n) (h0 : n ≠ 0) (hn : n ≤ 8) : E n i i = 2 := by
  interval_cases n
  <;> dsimp [E]
  <;> fin_cases i
  <;> decide

@[simp] theorem E_transpose (hn : n ≤ 8) : (E n).transpose = E n := by
  interval_cases n
  <;> decide

theorem E_isSymm (hn : n ≤ 8) : (E n).IsSymm := E_transpose hn

theorem isSimplyLaced_E (n : ℕ) (hn : n ≤ 8) : IsSimplyLaced (E n) := by
  interval_cases n
  <;> decide



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

/-- The principal submatrix of order 4 of \widetilde{E}₆. -/
def E_tilda₃ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0;
    -1, 2, 0, 0;
    0, 0, 2, -1;
    0, 0, -1, 2]

/-- The principal submatrix of order 5 of \widetilde{E}₆. -/
def E_tilda₄ : Matrix (Fin 5) (Fin 5) ℤ :=
  (A 5).reindex c[2, 4] c[2, 4]

/-- The principal submatrix of order 6 of \widetilde{E}₆. -/
def E_tilda₅ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, -1, 0, 0, 0, 0;
    -1, 2, 0, 0, -1, 0;
    0, 0, 2, -1, 0, 0;
    0, 0, -1, 2, -1, 0;
    0, -1, 0, -1, 2, -1;
    0, 0, 0, 0, -1, 2]

end CartanMatrix
