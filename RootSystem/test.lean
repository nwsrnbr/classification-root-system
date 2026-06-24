import Mathlib

variable {n : ℕ}

/-- A matrix `C` over `ℤ` is a **generalized Cartan matrix** if:
  1. Diagonal entries are 2.
  2. Off-diagonal entries are non-positive.
  3. `C i j = 0 ↔ C j i = 0` (symmetry of vanishing). -/
structure IsGeneralizedCartanMatrix {n : Type*} [DecidableEq n]
    (C : Matrix n n ℤ) : Prop where
  diag : ∀ i, C i i = 2
  off_diag_nonpos : ∀ i j, i ≠ j → C i j ≤ 0
  vanish_symm : ∀ i j, C i j = 0 ↔ C j i = 0

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

/-- The set of neighbors of vertex `u` in the Dynkin diagram. -/
def neighborSet (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => C i j ≠ 0 ∧ i ≠ j

def degree (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (neighborSet C i).card

/-- Two vertices are adjacent in the Dynkin diagram, excluding vertex `u`. -/
def adjExcl (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (i j : Fin n) : Prop :=
  i ≠ j ∧ i ≠ u ∧ j ≠ u ∧ C i j ≠ 0

/-- Vertex `w` is reachable from `v` in the Dynkin diagram with vertex `u` removed. -/
def reachExcl (C : Matrix (Fin n) (Fin n) ℤ) (u : Fin n) (v w : Fin n) : Prop :=
  Relation.ReflTransGen (adjExcl C u) v w

/-- The branch at `u` through `v`: all vertices reachable from `v` avoiding `u`. -/
def branchSet (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : Set (Fin n) :=
  {w | reachExcl C u v w}

/-- The number of vertices in the branch at `u` through `v`. -/
noncomputable def branchSize (C : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n) : ℕ :=
  Set.ncard (branchSet C u v)

/-
The smallest branch at a degree-3 vertex has exactly 1 vertex.
-/
theorem branciSize_inequality (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    1 / (branchSize C u v₁ + 1) +
    1 / (branchSize C u v₂ + 1) +
    1 / (branchSize C u v₃ + 1) > 1 := by
  sorry
