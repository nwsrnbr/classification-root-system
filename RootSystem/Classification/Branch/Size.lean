import RootSystem.Classification.DynkinGraph
import RootSystem.SymmMatrix.PosDef

variable {n : ℕ}

/-! ## Branch definition via reachability -/

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

/-! ## Branch structure lemmas -/

/-
If `branchSize ≥ 2`, the branch root `v` has a neighbor in the branch besides `u`.
-/
lemma branch_ge2_has_neighbor (C : Matrix (Fin n) (Fin n) ℤ)
    (u v : Fin n) (hbs : branchSize C u v ≥ 2) :
    ∃ z, z ≠ v ∧ z ≠ u ∧ C v z ≠ 0 ∧ z ∈ branchSet C u v := by
  -- Since `branchSize C u v` is at least 2,
  -- there exists some `w` in `branchSet C u v` such that `w ≠ v`.
  obtain ⟨w, hw⟩ : ∃ w ∈ branchSet C u v, w ≠ v := by
    contrapose! hbs
    exact lt_of_le_of_lt (
      Set.ncard_le_ncard (show branchSet C u v ⊆ { v } from fun x hx => hbs x hx)
    ) (by norm_num)
  -- Since `w ∈ branchSet C u v`, we have `TransGen (adjExcl C u) v w`.
  obtain ⟨z, hz⟩ : ∃ z, adjExcl C u v z ∧ reachExcl C u z w := by
    have := (hw.1).cases_head
    tauto
  use z
  exact ⟨ hz.1.1.symm, hz.1.2.2.1, hz.1.2.2.2, by exact Relation.ReflTransGen.single hz.1 ⟩

/-! ## Main branch bound theorems -/

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
    1 / branchSize C u v₁ + 1 / branchSize C u v₂ + 1 / branchSize C u v₃ > 1 := by
      sorry

/-
The smallest branch at a degree-3 vertex has exactly 1 vertex.
-/
theorem smallest_branch_eq_one (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃) :
    branchSize C u v₁ = 1 := by
  by_contra h_contra
  -- By branch_ge2_has_neighbor (applied to each vᵢ), for each i there exists wᵢ with:
  -- wᵢ ≠ vᵢ, wᵢ ≠ u, C vᵢ wᵢ ≠ 0.
  have hbs₁ : 2 ≤ branchSize C u v₁ := by
    rw [Nat.two_le_iff]
    exact ⟨Set.ncard_ne_zero_of_mem (
            show v₁ ∈ branchSet C u v₁ from
              Relation.ReflTransGen.refl
            ),
            h_contra⟩
  have hbs₂ : 2 ≤ branchSize C u v₂ := by linarith
  have hbs₃ : 2 ≤ branchSize C u v₃ := by linarith
  obtain ⟨w₁, hw₁⟩ := branch_ge2_has_neighbor C u v₁ hbs₁
  obtain ⟨w₂, hw₂⟩ := branch_ge2_has_neighbor C u v₂ hbs₂
  obtain ⟨w₃, hw₃⟩ := branch_ge2_has_neighbor C u v₃ hbs₃
  -- Show all 7 vertices {u, v₁, w₁, v₂, w₂, v₃, w₃} are distinct.
  have h_distinct : u ≠ v₁ ∧ u ≠ v₂ ∧ u ≠ v₃ ∧ u ≠ w₁ ∧ u ≠ w₂ ∧ u ≠ w₃ ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ w₁ ∧ v₁ ≠ w₂ ∧ v₁ ≠ w₃ ∧ v₂ ≠ v₃ ∧ v₂ ≠ w₁ ∧ v₂ ≠ w₂ ∧ v₂ ≠ w₃ ∧ v₃ ≠ w₁ ∧ v₃ ≠ w₂ ∧ v₃ ≠ w₃ ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ := by
    sorry
  --apply CartanMatrix.E_tilda₆_isNotPosDef
  let e : Fin 7 ↪ Fin n := Function.Embedding.mk ![u, v₁, w₁, v₂, w₂, v₃, w₃] (by
      simp [Function.Injective, Fin.forall_fin_succ]; grind)
  have hsub : (SymmMatrix C).submatrix e e = SymmMatrix CartanMatrix.E_tilda₆ := by
    ext i j
    fin_cases i
    <;> fin_cases j
    <;> simp [SymmMatrix, CartanMatrix.E_tilda₆, e]
  assumption

/-
The second-smallest branch at a degree-3 vertex has at most 2 vertices.
-/
theorem second_branch_le_two (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃) :
    branchSize C u v₂ ≤ 2 := by
  by_contra! hcontr;
  -- Use `branch_ge3_has_path2` on both `v₂` and `v₃` (with `hGCM`, `hP`, `u`, `vᵢ`, `C u vᵢ ≠ 0`, `u ≠ vᵢ`, `degree u = 3`, `branchSize ≥ 3`) to get:
  obtain ⟨x₂, y₂, hx₂, hy₂, hxy₂⟩ := branch_ge3_has_path2 C hGCM hP u v₂ (by
  exact Finset.mem_filter.mp hv₂ |>.2.1) (by
  unfold neighborSet at hv₂; aesop;) hu (by
  finiteness)
  obtain ⟨x₃, y₃, hx₃, hy₃, hxy₃⟩ := branch_ge3_has_path2 C hGCM hP u v₃ (by
  exact Finset.mem_filter.mp hv₃ |>.2.1) (by
  exact fun h => by simp_all +decide [ neighborSet ] ;) hu (by
  linarith);
  -- By the properties of the branch, we know that $x₂ \neq v₁$, $y₂ \neq v₁$, $x₃ \neq v₁$, and $y₃ \neq v₁$.
  have hx₂_ne_v₁ : x₂ ≠ v₁ := by
    rintro rfl;
    apply branches_disjoint C hGCM hP u v₂ x₂ hv₂ hv₁ (by tauto) x₂ (by tauto) (by tauto)
  have hy₂_ne_v₁ : y₂ ≠ v₁ := by
    intro H; simp_all +decide [ neighborSet ] ;
    have := branches_disjoint C hGCM hP u v₂ v₁; simp_all +decide [ branchSet ] ;
    exact this ( by unfold neighborSet; aesop ) ( by unfold neighborSet; aesop ) ( by tauto ) v₁ ( by tauto ) ( by tauto )
  have hx₃_ne_v₁ : x₃ ≠ v₁ := by
    intro H; simp_all +decide [ branchSet ] ;
    apply branches_disjoint C hGCM hP u v₃ v₁ hv₃ hv₁ (by tauto) v₁ (by tauto) (by tauto)
  have hy₃_ne_v₁ : y₃ ≠ v₁ := by
    intro h; simp_all +decide [ branchSet ] ;
    apply branches_disjoint C hGCM hP u v₃ v₁ hv₃ hv₁ (by tauto) v₁ (by tauto) (by tauto);
  -- By the properties of the branch, we know that $x₂ \neq v₃$, $x₃ \neq v₂$, $x₂ \neq x₃$, $y₂ \neq v₃$, $y₃ \neq v₂$, $x₂ \neq y₃$, $y₂ \neq x₃$, and $y₂ \neq y₃$.
  have hx₂_ne_v₃ : x₂ ≠ v₃ := by
    intro h;
    have := branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ ( by tauto ) v₃ ; simp_all +decide [ branchSet ];
    exact this ( Relation.ReflTransGen.refl )
  have hx₃_ne_v₂ : x₃ ≠ v₂ := by
    rintro rfl;
    apply branches_disjoint C hGCM hP u x₃ v₃ hv₂ hv₃ (by tauto) x₃ (by tauto) (by tauto)
  have hx₂_ne_x₃ : x₂ ≠ x₃ := by
    rintro rfl;
    apply branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ hdist.2.2 x₂ hxy₂.2.2.2.2.2.1 hxy₃.2.2.2.2.2.1
  have hy₂_ne_v₃ : y₂ ≠ v₃ := by
    intro h; simp_all +decide [ branchSet ] ;
    exact branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ ( by tauto ) v₃ ( by tauto ) ( by tauto )
  have hy₃_ne_v₂ : y₃ ≠ v₂ := by
    intro h; simp_all +decide [ branchSet ] ;
    have := branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ ( by tauto ) v₂ ( by tauto ) ( by tauto ) ; simp_all +decide [ branchSet ] ;
  have hx₂_ne_y₃ : x₂ ≠ y₃ := by
    intro h; simp_all +decide [ branchSet ] ;
    have := branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ hdist.2.2 y₃; simp_all +decide [ branchSet ] ;
  have hy₂_ne_x₃ : y₂ ≠ x₃ := by
    rintro rfl;
    apply branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ hdist.2.2 y₂ hxy₂.2.2.2.2.2.2 hxy₃.2.2.2.2.2.1
  have hy₂_ne_y₃ : y₂ ≠ y₃ := by
    rintro rfl;
    apply branches_disjoint C hGCM hP u v₂ v₃ hv₂ hv₃ hdist.2.2 y₂ hxy₂.2.2.2.2.2.2 hxy₃.2.2.2.2.2.2;
  -- Construct the embedding $f : Fin 8 ↪ Fin n$ with the specified properties.
  obtain ⟨f, hf⟩ : ∃ f : Fin 8 ↪ Fin n, f 0 = u ∧ f 1 = v₁ ∧ f 2 = v₂ ∧ f 3 = x₂ ∧ f 4 = y₂ ∧ f 5 = v₃ ∧ f 6 = x₃ ∧ f 7 = y₃ := by
    use ⟨![u, v₁, v₂, x₂, y₂, v₃, x₃, y₃], by
      simp +decide [ Function.Injective, Fin.forall_fin_succ ];
      grind +locals⟩
    generalize_proofs at *;
    exact ⟨ rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl ⟩;
  have h_adj : C (f 0) (f 1) ≠ 0 ∧ C (f 0) (f 2) ≠ 0 ∧ C (f 2) (f 3) ≠ 0 ∧ C (f 3) (f 4) ≠ 0 ∧ C (f 0) (f 5) ≠ 0 ∧ C (f 5) (f 6) ≠ 0 ∧ C (f 6) (f 7) ≠ 0 := by
    simp_all +decide [ neighborSet ];
  exact no_T133 C hGCM f h_adj.1 h_adj.2.1 h_adj.2.2.1 h_adj.2.2.2.1 h_adj.2.2.2.2.1 h_adj.2.2.2.2.2.1 h_adj.2.2.2.2.2.2 hP

/-- The largest branch at a degree-3 vertex has at most 4 vertices, provided
    the second-largest branch has at least 2 vertices.
    NOTE: The unconditional bound c ≤ 4 is FALSE: D_n with n ≥ 8 has
    branch sizes (1, 1, n-3) where n-3 ≥ 5. The bound only holds when b ≥ 2. -/
theorem largest_branch_le_four (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃)
    (hsort : branchSize C u v₁ ≤ branchSize C u v₂ ∧
             branchSize C u v₂ ≤ branchSize C u v₃)
    (hb : branchSize C u v₂ ≥ 2) :
    branchSize C u v₃ ≤ 4 := by
  sorry
