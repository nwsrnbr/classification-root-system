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

variable {ι E F : Type*} [Finite ι]
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (P : RootPairing ι ℝ E F) [P.IsCrystallographic] (b : P.Base)

theorem classification_root {n : ℕ} :
    CartanEquiv (CartanMatrix.A n) b.cartanMatrix ∨
    CartanEquiv (CartanMatrix.B n) b.cartanMatrix ∨
    CartanEquiv (CartanMatrix.C n) b.cartanMatrix ∨
    CartanEquiv (CartanMatrix.D n) b.cartanMatrix ∨
    CartanEquiv CartanMatrix.E₆ b.cartanMatrix ∨
    CartanEquiv CartanMatrix.E₇ b.cartanMatrix ∨
    CartanEquiv CartanMatrix.E₈ b.cartanMatrix ∨
    CartanEquiv CartanMatrix.F₄ b.cartanMatrix ∨
    CartanEquiv CartanMatrix.G₂ b.cartanMatrix := by
  sorry
