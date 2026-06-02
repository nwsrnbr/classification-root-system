import Mathlib.Tactic
import Mathlib.Data.Matrix.Cartan
import Mathlib.Tactic.FinCases
import RootSystem.SylvesterCriterion.SylvesterCriterion
import RootSystem.SymmMatrix.ExtendedDeterminant

namespace CartanMatrix

open Matrix

theorem A_isPosDef (n : ℕ) : (SymmMatrix (A n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, A_leadingSubmatrix, det_SymmMatrix_A]
  linarith

theorem B_isPosDef (n : ℕ) : (SymmMatrix (B n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, B_leadingSubmatrix]
  split_ifs
  · simp [det_SymmMatrix_B]
    grind
  · rw [det_SymmMatrix_A]
    linarith

theorem C_isPosDef (n : ℕ) : (SymmMatrix (C n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, C_leadingSubmatrix]
  split_ifs
  · simp [det_SymmMatrix_C]
    grind
  · rw [det_SymmMatrix_A]
    linarith

theorem D_isPosDef (n : ℕ) : (SymmMatrix (D n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, D_leadingSubmatrix]
  split_ifs
  · simp [det_SymmMatrix_D]
    grind
  · rw [det_SymmMatrix_A]
    linarith

theorem E₆_isPosDef : (SymmMatrix E₆).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, ← E, E_leadingSubmatrix (by norm_num),
      det_SymmMatrix_E k (by linarith)]
  split_ifs
  <;> simp; omega

theorem E₇_isPosDef : (SymmMatrix E₇).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, ← E, E_leadingSubmatrix (by norm_num),
      det_SymmMatrix_E k (by linarith)]
  split_ifs
  <;> simp; omega

theorem E₈_isPosDef : (SymmMatrix E₈).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, ← E, E_leadingSubmatrix (by norm_num),
      det_SymmMatrix_E k (by linarith)]
  split_ifs
  <;> simp; omega

theorem F₄_isPosDef : (SymmMatrix F₄).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm, F₄_leadingSubmatrix]
  split_ifs
  · apply lt_of_lt_of_eq zero_lt_one
    rw [← det_SymmMatrix_F₄]
    aesop
  · rw [det_SymmMatrix_B]
    grind
  · rw [det_SymmMatrix_A]
    linarith

theorem G₂_isPosDef : (SymmMatrix G₂).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm)]
  intro k hk _
  rw [SymmMatrix_leadingSubmatrix_comm]
  interval_cases k
  <;> dsimp [leadingSubmatrix]
  · apply lt_of_lt_of_eq zero_lt_two
    aesop
  · simp [det_SymmMatrix_G₂]



theorem A_tilda_isNotPosDef (n : ℕ) (hn : 2 ≤ n) : ¬(SymmMatrix (A_tilda n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use n + 1
  simp [leadingSubmatrix, det_SymmMatrix_A_tilda]
  grind

theorem B_tilda_isNotPosDef (n : ℕ) (hn : 3 ≤ n) : ¬(SymmMatrix (B_tilda n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use n + 1
  simp [leadingSubmatrix, det_SymmMatrix_B_tilda]
  grind

theorem C_tilda_isNotPosDef (n : ℕ) (hn : 2 ≤ n) : ¬(SymmMatrix (C_tilda n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use n + 1
  simp [leadingSubmatrix, det_SymmMatrix_C_tilda]
  grind

theorem D_tilda_isNotPosDef (n : ℕ) (hn : 5 ≤ n) : ¬(SymmMatrix (D_tilda n)).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use n + 1
  simp [leadingSubmatrix, det_SymmMatrix_D_tilda]
  grind

theorem E_tilda₆_isNotPosDef : ¬(SymmMatrix E_tilda₆).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use 7
  simp [leadingSubmatrix, det_SymmMatrix_E_tilda₆]

theorem E_tilda₇_isNotPosDef : ¬(SymmMatrix E_tilda₇).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use 8
  simp [leadingSubmatrix, det_SymmMatrix_E_tilda₇]

theorem E_tilda₈_isNotPosDef : ¬(SymmMatrix E_tilda₈).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use 9
  simp [leadingSubmatrix, det_SymmMatrix_E_tilda₈]

theorem F_tilda₄_isNotPosDef : ¬(SymmMatrix F_tilda₄).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use 5
  simp [leadingSubmatrix, det_SymmMatrix_F_tilda₄]

theorem G_tilda₂_isNotPosDef : ¬(SymmMatrix G_tilda₂).PosDef := by
  rw [sylvester_criterion (by apply SymmMatrix_isSymm), not_forall]
  use 3
  simp [leadingSubmatrix, det_SymmMatrix_G_tilda₂]

end CartanMatrix
