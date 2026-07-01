import RootSystem.Classification.DynkinGraph

/-! ### Connected components of an induced subgraph (for the combinatorial core) -/

/-- Reachability using only edges with both endpoints inside `S`. -/
def reachIn {n : ℕ} (adj : Fin n → Fin n → Prop) (S : Finset (Fin n)) (w z : Fin n) : Prop :=
  Relation.ReflTransGen (fun i j => i ∈ S ∧ j ∈ S ∧ adj i j) w z

attribute [local instance] Classical.propDecidable

/-- The connected component of `w` inside `S`. -/
noncomputable def compIn {n : ℕ} (adj : Fin n → Fin n → Prop)
    (S : Finset (Fin n)) (w : Fin n) : Finset (Fin n) :=
  S.filter (fun z => reachIn adj S w z)

lemma reachIn_refl {n : ℕ} (adj : Fin n → Fin n → Prop) (S : Finset (Fin n)) (w : Fin n) :
    reachIn adj S w w := Relation.ReflTransGen.refl

lemma reachIn_symm {n : ℕ} {adj : Fin n → Fin n → Prop} (hsymm : ∀ i j, adj i j → adj j i)
    {S : Finset (Fin n)} {w z : Fin n} (h : reachIn adj S w z) : reachIn adj S z w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hsymm _ _ hbc.2.2⟩ ih

lemma reachIn_trans {n : ℕ} {adj : Fin n → Fin n → Prop} {S : Finset (Fin n)} {a b c : Fin n}
    (h1 : reachIn adj S a b) (h2 : reachIn adj S b c) : reachIn adj S a c :=
  Relation.ReflTransGen.trans h1 h2

/-
**Connected components partition.**  The set of components of `S` partitions `S`,
with no edges between distinct components.
-/
lemma exists_components {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hsymm : ∀ i j, adj i j → adj j i) (S : Finset (Fin n)) :
    ∃ P : Finset (Finset (Fin n)),
      (∀ C ∈ P, C ⊆ S) ∧
      (∀ C ∈ P, C.Nonempty) ∧
      (S = P.biUnion id) ∧
      (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
      (∀ C ∈ P, ∀ w ∈ C, ∀ z, z ∈ C ↔ (z ∈ S ∧ reachIn adj S w z)) ∧
      (∀ C ∈ P, ∀ w ∈ C, ∀ z ∈ S, adj w z → z ∈ C) := by
  refine' ⟨
    Finset.image (fun w => compIn adj S w) (Finset.filter ( fun w => w ∈ S ) Finset.univ),
    _, _, _, _, _, _
  ⟩
  <;> simp [Finset.subset_iff]
  · simp only [compIn]
    aesop
  · intro w hw
    use w
    simp [compIn, hw, reachIn_refl]
  · ext w
    simp [compIn]
    exact ⟨ fun hw => ⟨ w, hw, hw, reachIn_refl _ _ _ ⟩, by rintro ⟨ a, ha, hw, h ⟩ ; exact hw ⟩
  · intro a ha b hb hab
    rw [Finset.disjoint_left]
    contrapose! hab
    simp_all [Finset.ext_iff, compIn]
    obtain ⟨c, hc₁, hc₂, hc₃⟩ := hab
    apply reachIn_symm hsymm at hc₃
    apply reachIn_trans hc₁.2 at hc₃
    exact fun x hx => ⟨
      fun h => reachIn_trans (reachIn_symm hsymm hc₃) h, fun h => reachIn_trans hc₃ h
    ⟩
  · simp [compIn]
    intro a ha w hw haw z hz
    constructor
    <;> intro h
    · exact reachIn_trans (reachIn_symm hsymm haw) h
    · exact reachIn_trans haw h
  · simp [compIn]
    exact fun a ha w hw h₁ z hz h₂ => ⟨hz, h₁.trans (Relation.ReflTransGen.single ⟨hw, hz, h₂⟩)⟩

/-- A within-`S` path from `w` stays inside the component `compIn adj S w`. -/
lemma reachIn_confine {n : ℕ} {adj : Fin n → Fin n → Prop} {S : Finset (Fin n)} {w z : Fin n}
    (h : reachIn adj S w z) : reachIn adj (compIn adj S w) w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hwb hbc ih =>
      have hbmem : b ∈ compIn adj S w :=
        Finset.mem_filter.2 ⟨hbc.1, hwb⟩
      have hcmem : c ∈ compIn adj S w :=
        Finset.mem_filter.2 ⟨hbc.2.1, hwb.tail hbc⟩
      exact ih.tail ⟨hbmem, hcmem, hbc.2.2⟩

/-- From a within-`K` path out of `r` to some `w ≠ r`, extract a neighbour `z` of
`r` lying in `K.erase r` that reaches `w` without using `r`. -/
lemma exists_first_neighbor {n : ℕ} {adj : Fin n → Fin n → Prop}
    {K : Finset (Fin n)} {r w : Fin n} (h : reachIn adj K r w) (hw : w ≠ r) :
    ∃ z, adj r z ∧ z ∈ K.erase r ∧ reachIn adj (K.erase r) z w := by
  induction h with
  | refl => simp at hw
  | @tail b c hrb hbc ih =>
      rcases eq_or_ne b r with hbr | hbr
      · subst hbr
        exact ⟨c, hbc.2.2, Finset.mem_erase.2 ⟨hw, hbc.2.1⟩, Relation.ReflTransGen.refl⟩
      · obtain ⟨z, hz1, hz2, hz3⟩ := ih hbr
        exact ⟨z, hz1, hz2, hz3.tail ⟨Finset.mem_erase.2 ⟨hbr, hbc.1⟩,
          Finset.mem_erase.2 ⟨hw, hbc.2.1⟩, hbc.2.2⟩⟩

lemma branch_weight_exists {n : ℕ} {adj : Fin n → Fin n → Prop}
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (K : Finset (Fin n)) (r : Fin n) (hr : r ∈ K)
    (hconn : ∀ w ∈ K, reachIn adj K r w)
    (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C) :
    ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, i ∉ K → y i = 0) ∧
      y r = (K.card : ℝ) / (K.card + 1) ∧
      (∀ i, i ∈ K → i ≠ r → 0 < y i →
        2 * y i ≤ ∑ j with j ∈ neighborSet C i ∩ K, y j) := by
  sorry
