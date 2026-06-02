import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Cartan
import RootSystem.Cartan.LeadingSubmatrix

open Matrix

variable {n : ℕ} {k : ℕ} {hk : k ≤ n} {C : Matrix (Fin n) (Fin n) ℤ}

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

lemma SymmMatrix_isSymm : (SymmMatrix C).IsSymm := by
  ext i j
  simp [SymmMatrix, mul_comm]
  aesop

lemma SymmMatrix_eq_rfl (hsymm : C.IsSymm) (hd : ∀ i, C i i = 2) (hsimp : C.IsSimplyLaced) :
    SymmMatrix C = (C.map (↑)) := by
  ext i j
  dsimp [SymmMatrix]
  by_cases hij : i = j
  · simp [hij, hd]
  · simp only [hij]
    dsimp [IsSimplyLaced, Pairwise] at hsimp
    rcases (hsimp hij) with h | h
    <;> simp [h, hsymm.apply]

lemma det_SymmMatrix_eq_rfl (hsymm : C.IsSymm) (hd : ∀ i, C i i = 2) (hsimp : C.IsSimplyLaced) :
    (SymmMatrix C).det = C.det := by
  simp only [SymmMatrix_eq_rfl hsymm hd hsimp]
  apply Eq.symm (Int.cast_det C)

lemma SymmMatrix_leadingSubmatrix_comm :
    (SymmMatrix C).leadingSubmatrix k hk = SymmMatrix (C.leadingSubmatrix k hk) := by
  ext i j
  simp [SymmMatrix, leadingSubmatrix]

namespace CartanMatrix

lemma SymmMatrix_A_isTopLeftBlock :
    isTopLeftBlock (SymmMatrix (A (n + 1))) = SymmMatrix (A n) := by
  rw [isTopLeftBlock_eq, SymmMatrix_leadingSubmatrix_comm, A_leadingSubmatrix]

lemma SymmMatrix_B_isTopLeftBlock :
    isTopLeftBlock (SymmMatrix (B (n + 1))) = SymmMatrix (A n) := by
  simp [isTopLeftBlock_eq, SymmMatrix_leadingSubmatrix_comm, B_leadingSubmatrix]

lemma SymmMatrix_D_rev_isTopLeftBlock :
    isTopLeftBlock (SymmMatrix (D_rev (n + 1))) = SymmMatrix (D_rev n) := by
  rw [isTopLeftBlock_eq, SymmMatrix_leadingSubmatrix_comm, D_rev_leadingSubmatrix]

lemma SymmMatrix_E_isTopLeftBlock (hn : n + 1 ≤ 8) :
    isTopLeftBlock (SymmMatrix (E (n + 1))) = SymmMatrix (E n) := by
  rw [isTopLeftBlock_eq, SymmMatrix_leadingSubmatrix_comm, E_leadingSubmatrix hn]

lemma SymmMatrix_F₄_isTopLeftBlock :
    isTopLeftBlock (SymmMatrix F₄) = SymmMatrix (B 3) := by
  simp [isTopLeftBlock_eq, SymmMatrix_leadingSubmatrix_comm, F₄_leadingSubmatrix]

end CartanMatrix
