import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.PosDef
import RootSystem.Classification.GCM
import RootSystem.SymmMatrix.Basic

variable {n : ℕ}

/-- The Dynkin graph of a generalized Cartan matrix: vertices are `Fin n`,
    and `i` is adjacent to `j` iff `C i j ≠ 0` (and `i ≠ j`). -/
def dynkinGraph (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) : SimpleGraph (Fin n) where
  Adj i j := C i j ≠ 0 ∧ i ≠ j
  symm i j h := ⟨fun h_eq => h.1 ((hGCM.vanish_symm j i).mp h_eq), h.2.symm⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-
An indecomposable GCM has a connected Dynkin graph.
-/
lemma dynkinGraph_preconnected (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hI : IsIndecomposable C) :
    (dynkinGraph C hGCM).Preconnected := by
  intro u v
  by_contra h_not_reachable
  set S := {w | (dynkinGraph C hGCM).Reachable u w}
  have hS_nonempty : S.Nonempty := by
    exact ⟨ u, SimpleGraph.Reachable.refl _ ⟩
  have hS_univ : S = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro w
    by_contra hw_not_in_S
    have hS_not_univ : S ≠ Set.univ := by
      exact Set.nonempty_compl.1 ⟨ w, hw_not_in_S ⟩
    have hS_not_univ' : ∃ i ∈ S, ∃ j ∉ S, C i j ≠ 0 := by
      exact hI S hS_nonempty.ne_empty hS_not_univ |> fun ⟨ i, hi, j, hj, h ⟩ => ⟨ i, hi, j, hj, h ⟩
    obtain ⟨i, hiS, j, hjS, hCij⟩ := hS_not_univ'
    have h_adj : (dynkinGraph C hGCM).Adj i j := by
      exact ⟨ hCij, by rintro rfl; exact hjS <| hiS ⟩
    have h_reachable : (dynkinGraph C hGCM).Reachable u j := by
      exact hiS.trans ( SimpleGraph.Adj.reachable h_adj )
    exact hjS h_reachable
  have h_contra : v ∈ S := by
    exact hS_univ.symm.subset <| Set.mem_univ v
  exact h_not_reachable h_contra


def degree (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  ((Finset.univ.filter fun j => C i j ≠ 0 ∧ i ≠ j).card)

def IsBranch (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Prop :=
  3 ≤ degree C i

instance IsBranch.decidable (C : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Decidable (IsBranch C i) :=
  inferInstanceAs (Decidable (3 ≤ degree C i))

def numOfBranch (C : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  (Finset.univ.filter (fun i => IsBranch C i)).card
