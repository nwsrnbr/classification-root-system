import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Cartan
import RootSystem.Cartan.Auxiliary

namespace CartanMatrix

open Matrix

variable (n : ℕ)

/-- The Cartan matrix of type \widetilde{A}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    ┌---------- o ------------┐
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def A_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (A n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (i.val = 0 ∧ j.val = n) ∨ (j.val = 0 ∧ i.val = n) ∨
            (i.val = n - 1 ∧ j.val = n) ∨ (j.val = n - 1 ∧ i.val = n) then -1
    else 0

/-- The Cartan matrix of type \widetilde{B}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o
     \
      o --- o ⬝ ⬝ ⬝ ⬝ o =>= o
     /
    o
```
-/
def B_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (D_rev n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i then -1
    else if (i : ℕ) + 1 = j then -2
    else 0

/-- The Cartan matrix of type \widetilde{C}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```

    o =>= o --- o ⬝ ⬝ ⬝ ⬝ o =<= o
```
-/
def C_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (rev (C n)) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i then -2
    else if (i : ℕ) + 1 = j then -1
    else 0

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
def D_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n - 2 ∧ j < n - 2 then (D_rev n) (i.castLT (by omega)) (j.castLT (by omega))
    else if i = j then 2
    else if i.val + 1 = n ∧ (j.val + 3 = n ∨ j.val + 2 = n ∨ j.val = n) then -1
    else if j.val + 1 = n ∧ (i.val + 3 = n ∨ i.val + 2 = n ∨ i.val = n) then -1
    else 0

/-- The Cartan matrix of type \widetilde{E}₆.

The corresponding Dynkin diagram is:
```
            o
            |
            o
            |
o --- o --- o --- o --- o
```
-/
def E_tilda₆ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0;
    -1, 2, 0, 0, -1, 0, 0;
    0, 0, 2, -1, 0, 0, 0;
    0, 0, -1, 2, -1, 0, 0;
    0, -1, 0, -1, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type \widetilde{E}₇.

The corresponding Dynkin diagram is:
```
                  o
                  |
o --- o --- o --- o --- o --- o --- o
```
-/
def E_tilda₇ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0, 0;
    0, 0, -1, 2, -1, -1, 0, 0;
    0, 0, 0, -1, 2, 0, -1, 0;
    0, 0, 0, -1, 0, 2, 0, 0;
    0, 0, 0, 0, -1, 0, 2, -1;
    0, 0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type \widetilde{E}₈.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o --- o --- o
```
-/
def E_tilda₈ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type \widetilde{F}₄.

The corresponding Dynkin diagram is:
```
o --- o --- o =>= o --- o
```
-/
def F_tilda₄ : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, -1, 0, 0, 0;
    -1, 2, -2, 0, 0;
    0, -1, 2, -1, 0;
    0, 0, -1, 2, -1;
    0, 0, 0, -1, 2]

/-- The Cartan matrix of type \widetilde{G}₂.

The corresponding Dynkin diagram is:
```
o --- o ≡>≡ o
```
Actually we are using the transpose of Bourbaki's matrix. This is to make this matrix consistent
with `CartanMatrix.F₄`, in the sense that all non-zero values below the diagonal are -1. -/
def G_tilda₂ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, -3, 0;
    -1, 2, -1;
    0, -1, 2]

/-! ### Properties -/

section Properties

variable (n : ℕ)

@[simp] theorem A_tilda_diag (i : Fin (n + 1)) : A_tilda n i i = 2 := by
  simp [A_tilda, A, of_apply]
@[simp] theorem B_tilda_diag (i : Fin (n + 1)) : B_tilda n i i = 2 := by
  simp [B_tilda, D_rev, of_apply]
@[simp] theorem C_tilda_diag (i : Fin (n + 1)) : C_tilda n i i = 2 := by
  simp [C_tilda, C, rev, of_apply]
@[simp] theorem D_tilda_diag (i : Fin (n + 1)) : D_tilda n i i = 2 := by
  simp [D_tilda, D_rev, of_apply]

/-! ### Transpose properties -/

@[simp] theorem A_tilda_transpose : (A_tilda n).transpose = A_tilda n := by
  ext; simp only [A_tilda, A, transpose_apply, of_apply]; grind

theorem A_tilda_isSymm : (A_tilda n).IsSymm := A_tilda_transpose n

@[simp] theorem D_tilda_transpose : (D_tilda n).transpose = D_tilda n := by
  ext; simp only [D_tilda, D_rev, transpose_apply, of_apply]; grind

theorem D_tilda_isSymm : (D_tilda n).IsSymm := D_tilda_transpose n

/-! ### Exceptional matrix diagonal entries -/

@[simp] theorem E_tilda₆_diag (i : Fin 7) : E_tilda₆ i i = 2 := by fin_cases i <;> decide

@[simp] theorem E_tilda₇_diag (i : Fin 8) : E_tilda₇ i i = 2 := by fin_cases i <;> decide

@[simp] theorem E_tilda₈_diag (i : Fin 9) : E_tilda₈ i i = 2 := by fin_cases i <;> decide

@[simp] theorem F_tilda₄_diag (i : Fin 5) : F_tilda₄ i i = 2 := by fin_cases i <;> decide

@[simp] theorem G_tilda₂_diag (i : Fin 3) : G_tilda₂ i i = 2 := by fin_cases i <;> decide

/-! ### Exceptional matrix transpose properties -/

@[simp] theorem E_tilda₆_transpose : E_tilda₆.transpose = E_tilda₆ := by decide
@[simp] theorem E_tilda₇_transpose : E_tilda₇.transpose = E_tilda₇ := by decide
@[simp] theorem E_tilda₈_transpose : E_tilda₈.transpose = E_tilda₈ := by decide

theorem E_tilda₆_isSymm : E_tilda₆.IsSymm := E_tilda₆_transpose
theorem E_tilda₇_isSymm : E_tilda₇.IsSymm := E_tilda₇_transpose
theorem E_tilda₈_isSymm : E_tilda₈.IsSymm := E_tilda₈_transpose



theorem isSimplyLaced_A_tilda (n : ℕ) : IsSimplyLaced (A_tilda n) := by
  intro i j h
  simp only [A_tilda, A, of_apply]
  grind

theorem isSimplyLaced_D_tilda (n : ℕ) : IsSimplyLaced (D_tilda n) := by
  intro i j h
  simp only [D_tilda, D_rev, of_apply]
  grind

theorem isSimplyLaced_E_tilda₆ : IsSimplyLaced E_tilda₆ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E_tilda₆ E_tilda₆_isSymm]; decide

theorem isSimplyLaced_E_tilda₇ : IsSimplyLaced E_tilda₇ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E_tilda₇ E_tilda₇_isSymm]; decide

theorem isSimplyLaced_E_tilda₈ : IsSimplyLaced E_tilda₈ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E_tilda₈ E_tilda₈_isSymm]; decide

end Properties

end CartanMatrix
