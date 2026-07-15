import RootSystem.Classification.GCM
import RootSystem.SymmMatrix.PosDef

/-- The classification of indecomposable generalized Cartan matrices of finite type:
every such matrix (with index set `Fin m`) is Cartan-equivalent to one of the standard types. -/
theorem classification_cartan {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (hIndec : IsIndecomposable C)
    (hPosDef : (SymmMatrix C).PosDef) :
    CartanEquiv (CartanMatrix.A n) C ∨
    CartanEquiv (CartanMatrix.B n) C ∨
    CartanEquiv (CartanMatrix.C n) C ∨
    CartanEquiv (CartanMatrix.D n) C ∨
    CartanEquiv CartanMatrix.E₆ C ∨
    CartanEquiv CartanMatrix.E₇ C ∨
    CartanEquiv CartanMatrix.E₈ C ∨
    CartanEquiv CartanMatrix.F₄ C ∨
    CartanEquiv CartanMatrix.G₂ C := by
  sorry
