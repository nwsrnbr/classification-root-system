import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Cartan
import RootSystem.Cartan.Determinant
import RootSystem.SymmMatrix.Determinant

namespace CartanMatrix

open Matrix

variable (n : ℕ)

lemma det_C_rev : (rev (C n)).det = (C n).det := by
  simp [det_rev]

/-- The Cartan matrix of type \widetilde{A}ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    ┌---------- o ------------┐
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def A_tilda : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 2
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1
        else (if i = (0 : ℕ) ∧ j = n ∨ j = (0 : ℕ) ∧ i = n then -1 else 0))

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
    else if (j : ℕ) + 1 = i then -2
    else if (i : ℕ) + 1 = j then -1
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
    else if (j : ℕ) + 1 = i then -1
    else if (i : ℕ) + 1 = j then -2
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
    if h : i < n ∧ j < n then (D_rev n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 2 = i then -1
    else if (i : ℕ) + 2 = j then -1
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
    -1, 2, -1, 0, 0, 0, 0;
    0, -1, 2, -1, 0, -1, 0;
    0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, -1, 2, 0, 0;
    0, 0, -1, 0, 0, 2, -1;
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
    0, 0, 0, -1, 2, 0, 0, 0;
    0, 0, 0, -1, 0, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1;
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
  !![2, -1, 0, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0, 0;
    0, -1, 2, -1, -1, 0, 0, 0, 0;
    0, 0, -1, 2, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 2, -1, 0, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, 0, 0, -1, 2]

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

/-

-/
end CartanMatrix
