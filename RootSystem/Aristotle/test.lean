import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

import Mathlib.Data.Matrix.Cartan

variable {ι E F : Type*} [DecidableEq ι]

noncomputable def SymmMatrix (C : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  Matrix.of fun i j : ι ↦
    if i = j then 2
    else -√(C i j * C j i)

variable {E F : Type*}
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (P : RootPairing ι ℝ E F) [P.IsCrystallographic] (b : P.Base)

lemma root_cartan_pos : (SymmMatrix b.cartanMatrix).PosDef := by
  sorry
