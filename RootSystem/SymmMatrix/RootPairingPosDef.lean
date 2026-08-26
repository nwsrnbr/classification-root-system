import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

open Matrix

variable {ι : Type*} [DecidableEq ι]

noncomputable def SymmMatrix' (C : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  Matrix.of fun i j : ι ↦
    if i = j then 2
    else -√(C i j * C j i)

-- lemma cartan_PosDef_iff (d : ι → ℤ) (hd : ∀ i, 0 < d i) (C : Matrix ι ι ℤ) :
--     (SymmMatrix' (diagonal d * C)).PosDef ↔ (SymmMatrix' C).PosDef := by
--   have h : SymmMatrix' (d ⬝ᵥ C) = d ⬝ᵥ SymmMatrix' C := by
--     ext i j
--     simp [SymmMatrix', Matrix.smul_apply]
--   rw [h]
--   exact Matrix.PosDef.smul_iff hd
