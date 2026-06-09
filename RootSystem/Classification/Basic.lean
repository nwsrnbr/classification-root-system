import RootSystem.Classification.GCM
import RootSystem.SymmMatrix.PosDef

/-- The classification of indecomposable generalized Cartan matrices of finite type:
every such matrix (with index set `Fin m`) is Cartan-equivalent to one of the standard types. -/
theorem classification_cartan (m : ℕ) (C : Matrix (Fin m) (Fin m) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C)
    (hIndec : IsIndecomposable C)
    (hPosDef : (SymmMatrix C).PosDef) :
    (∃ n, CartanEquiv (CartanMatrix.A n) C) ∨
    (∃ n, CartanEquiv (CartanMatrix.B n) C) ∨
    (∃ n, CartanEquiv (CartanMatrix.C n) C) ∨
    (∃ n, CartanEquiv (CartanMatrix.D n) C) ∨
    CartanEquiv CartanMatrix.E₆ C ∨
    CartanEquiv CartanMatrix.E₇ C ∨
    CartanEquiv CartanMatrix.E₈ C ∨
    CartanEquiv CartanMatrix.F₄ C ∨
    CartanEquiv CartanMatrix.G₂ C := by
  sorry
