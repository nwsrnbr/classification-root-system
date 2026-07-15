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
    Finset.image (fun w => compIn adj S w) (Finset.filter (fun w => w ∈ S) Finset.univ),
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

/-! ### Combinatorial core: rooted energy of a connected graph -/

/-
Square-sum of a weighting built from a partition splits as the root term plus
the per-component square sums.
-/
lemma combined_sq_sum {n : ℕ} (P : Finset (Finset (Fin n))) (S K : Finset (Fin n)) (r : Fin n)
    (a : ℝ) (f : Finset (Fin n) → Fin n → ℝ)
    (hrS : r ∉ S) (hK : K = insert r S) (hSP : S = P.biUnion id)
    (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
    (g : Fin n → ℝ)
    (hg : ∀ i, g i = if i = r then a else ∑ C ∈ P, if i ∈ C then f C i else 0) :
    ∑ i ∈ K, (g i) ^ 2 = a ^ 2 + ∑ C ∈ P, ∑ i ∈ C, (f C i) ^ 2 := by
  simp only [*]
  rw [Finset.sum_insert]
  <;> norm_num [hSP]
  · rw [Finset.sum_biUnion]
    · refine' Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun i hi => _;
      rw [Finset.sum_eq_single C]
      <;> simp_all [Finset.disjoint_left]
      · grind
      · exact fun D hD hDC hiD => False.elim <| hdisj _ hD _ hC hDC hiD hi;
    · exact fun x hx y hy hxy => hdisj x hx y hy hxy;
  · exact fun C hC => fun h => hrS <| hSP.symm ▸ Finset.mem_biUnion.mpr ⟨ C, hC, h ⟩

/-
Cross/quadratic term of a weighting built from a partition: with no edges
between distinct components, it splits into per-component quadratic terms plus the
root-to-component coupling.
-/
lemma combined_cross_sum {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (P : Finset (Finset (Fin n))) (S K : Finset (Fin n)) (r : Fin n)
    (a : ℝ) (f : Finset (Fin n) → Fin n → ℝ)
    (hrS : r ∉ S) (hK : K = insert r S) (hSP : S = P.biUnion id)
    (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
    (hsupp : ∀ C ∈ P, ∀ i, i ∉ C → f C i = 0)
    (hcross : ∀ C ∈ P, ∀ i ∈ C, ∀ j ∈ S, adj i j → j ∈ C)
    (g : Fin n → ℝ)
    (hg : ∀ i, g i = if i = r then a else ∑ C ∈ P, if i ∈ C then f C i else 0) :
    ∑ i ∈ K, ∑ j ∈ K, (if adj i j then g i * g j else 0) =
      (∑ C ∈ P, ∑ i ∈ C, ∑ j ∈ C, (if adj i j then f C i * f C j else 0))
        + 2 * a * ∑ C ∈ P, ∑ i ∈ C, (if adj r i then f C i else 0) := by
  -- Using the definition of $g$ from $hg$, we can expand the sums and simplify.
  have h_expand : (∑ i ∈ K, ∑ j ∈ K, if adj i j then g i * g j else 0)
      = (∑ i ∈ S, ∑ j ∈ S, if adj i j then (∑ C ∈ P, (if i ∈ C then f C i else 0))
        * (∑ D ∈ P, (if j ∈ D then f D j else 0)) else 0)
        + 2 * a * (∑ i ∈ S, if adj r i then (∑ C ∈ P, (if i ∈ C then f C i else 0)) else 0) := by
    simp [hK, hg, Finset.sum_insert hrS]
    simp [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, hirr, Finset.sum_ite]
    ring_nf
    simp [Finset.filter_eq', Finset.filter_ne', hrS, hirr, Finset.sum_filter,
      Finset.sum_add_distrib, mul_two, add_assoc]
    ring_nf!
    grind +qlia
  convert h_expand using 2
  · -- Apply the disjointness of the components to split the sum.
    have h_split_sum : ∑ i ∈ S, ∑ j ∈ S, (if adj i j then (∑ C ∈ P, (if i ∈ C then f C i else 0))
          * (∑ D ∈ P, (if j ∈ D then f D j else 0)) else 0)
        = ∑ C ∈ P, ∑ i ∈ C, ∑ j ∈ C, (if adj i j then (∑ D ∈ P, (if i ∈ D then f D i else 0))
          * (∑ E ∈ P, (if j ∈ E then f E j else 0)) else 0) := by
      rw [hSP, Finset.sum_biUnion]
      · refine' Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun i hi => _
        rw [← Finset.sum_subset
          (show C ⊆ P.biUnion id from fun x hx => Finset.mem_biUnion.mpr ⟨C, hC, hx⟩)]
        grind
      · exact fun x hx y hy hxy => hdisj x hx y hy hxy
    convert h_split_sum.symm using 3
    refine' Finset.sum_congr rfl fun j hj => _
    rw [Finset.sum_eq_single ‹_›, Finset.sum_eq_single ‹_›]
    <;> simp +contextual [*]
    · exact fun C hC hne hjC => False.elim <| Finset.disjoint_left.mp (hdisj _ hC _ ‹_› hne) hjC hj;
    · exact fun C hC hne hi => hsupp C hC _ (fun hi' => Finset.disjoint_left.mp (hdisj _ hC _ ‹_› hne) hi' ‹_›);
  · simp [Finset.sum_ite, Finset.filter_congr, hSP]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine' Or.inl (Finset.sum_bij (fun x hx => ⟨ x.snd, x.fst ⟩) _ _ _ _)
    <;> simp +contextual
    · exact fun a ha₁ ha₂ ha₃ => ⟨ _, ha₁, ha₂ ⟩;
    · bound;
    · exact fun b x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ _, _, ⟨ hx₄, hx₅, hx₃ ⟩, rfl ⟩


/-
Scalar arithmetic core of the induction step: combining the per-component
energy lower bounds yields the root bound, reducing to a sum-of-squares estimate.
-/
lemma energy_scalar {ix : Type*} (N : ℕ) (hN : 2 ≤ N) (P : Finset ix) (t : ix → ℕ)
    (Sq Ad R : ix → ℝ)
    (hsum : ∑ C ∈ P, (t C : ℝ) = (N : ℝ) - 1)
    (hAS : ∀ C ∈ P, -((t C : ℝ) / (t C + 1)) ≤ Ad C - 2 * Sq C)
    (hR : ∀ C ∈ P, (t C : ℝ) / (t C + 1) ≤ R C) :
    (N : ℝ) / (N + 1) ≤
      2 * ((N : ℝ) / (N + 1))
        - 2 * (((N : ℝ) / (N + 1)) ^ 2
            + ∑ C ∈ P, (((t C : ℝ) + 1) / (N + 1)) ^ 2 * Sq C)
        + ((∑ C ∈ P, (((t C : ℝ) + 1) / (N + 1)) ^ 2 * Ad C)
            + 2 * ((N : ℝ) / (N + 1)) * ∑ C ∈ P, (((t C : ℝ) + 1) / (N + 1)) * R C) := by
  -- Combine the two component sums into one and bound termwise.
  suffices h_sum_bound : (∑ C ∈ P, ((t C + 1 : ℝ) / (N + 1)) ^ 2 * (Ad C - 2 * Sq C)
        + 2 * (N / (N + 1)) * (∑ C ∈ P, ((t C + 1) / (N + 1)) * R C))
      ≥ (∑ C ∈ P, ((t C + 1 : ℝ) / (N + 1)) ^ 2 * (-(t C / (t C + 1 : ℝ)))
        + 2 * (N / (N + 1)) * (∑ C ∈ P, ((t C + 1) / (N + 1)) * (t C / (t C + 1 : ℝ)))) by
    -- Simplify the per-term right side in closed form.
    have h_simplify : (∑ C ∈ P, ((t C + 1 : ℝ) / (N + 1)) ^ 2 * (-(t C / (t C + 1 : ℝ)))
          + 2 * (N / (N + 1)) * (∑ C ∈ P, ((t C + 1) / (N + 1)) * (t C / (t C + 1 : ℝ))))
        = (2 * N * (∑ C ∈ P, (t C : ℝ)) - (∑ C ∈ P, (t C : ℝ) ^ 2)
          - (∑ C ∈ P, (t C : ℝ))) / (N + 1) ^ 2 := by
      rw [Finset.mul_sum _ _ _]
      rw [← Finset.sum_add_distrib, Finset.mul_sum _ _ _, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, Finset.sum_div]
      congr
      ext x
      ring_nf
      -- Combine like terms and simplify the expression.
      field_simp
      ring
    -- Apply the inequality $\sum_{C \in P} t_C^2 \leq (\sum_{C \in P} t_C)^2$.
    have h_sum_sq : (∑ C ∈ P, (t C : ℝ) ^ 2) ≤ (∑ C ∈ P, (t C : ℝ)) ^ 2 := by
      simpa only [sq, Finset.sum_mul _ _ _]
        using Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun a _ => Nat.cast_nonneg (t a)) hi) (Nat.cast_nonneg (t i))
    simp_all [mul_sub]
    field_simp at *;
    norm_num [← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_div_assoc] at *
    nlinarith [(by norm_cast : (2 : ℝ) ≤ N)]
  exact add_le_add (Finset.sum_le_sum fun C hC => mul_le_mul_of_nonneg_left
    (hAS C hC) (sq_nonneg _)) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
    fun C hC => mul_le_mul_of_nonneg_left (hR C hC) (by positivity)) (by positivity))


/-
**Rooted energy bound (strengthened).**  For a finite connected graph (`adj`,
symmetric, irreflexive) on a vertex set `K` with a chosen root `r`, there is a
nonnegative weighting `y` supported on `K`, with `y r = |K|/(|K|+1)`, whose rooted
energy `2 y_r - 2 Σ y_i² + Σ [adj i j] y_i y_j` is at least `|K|/(|K|+1)`.  Tight
for a path rooted at an endpoint; the heart of the branch inequality.
-/
lemma branch_energy_strong {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (K : Finset (Fin n)) (r : Fin n) (hr : r ∈ K)
    (hconn : ∀ w ∈ K, reachIn adj K r w) :
    ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i, i ∉ K → y i = 0) ∧
      y r = (K.card : ℝ) / (K.card + 1) ∧
      (K.card : ℝ) / (K.card + 1) ≤
        2 * y r - 2 * (∑ i ∈ K, (y i) ^ 2)
          + (∑ i ∈ K, ∑ j ∈ K, if adj i j then y i * y j else 0) := by
  -- By induction on the size of the set $K$.
  have h_ind_step : ∀ N : ℕ, ∀ (K : Finset (Fin n)),
      K.card = N → ∀ r ∈ K, ∀ (hconn : ∀ w ∈ K, reachIn adj K r w),
      ∃ y : Fin n → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ i ∉ K, y i = 0) ∧ y r = N / (N + 1) ∧
        (N : ℝ) / (N + 1)
        ≤ 2 * y r - 2 * ∑ i ∈ K, y i ^ 2 + ∑ i ∈ K, ∑ j ∈ K, (if adj i j then y i * y j else 0) := by
    intro N K hK r hr hconn
    induction' N using Nat.strong_induction_on with N ih generalizing K r
    by_cases hN : N ≤ 1
    · interval_cases N
      <;> simp_all
      refine' ⟨fun i => if i = r then 1 / 2 else 0, _, _, _, _⟩
      <;> norm_num [hr, hK]
      · intro i; split_ifs <;> norm_num;
      · exact fun i hi => by rintro rfl; exact hi hr;
      · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num;
    · obtain ⟨P, hP⟩ := exists_components adj hsymm (K.erase r)
      -- For each component $C \in P$, choose a vertex $r_C \in C$ such that $adj r r_C$.
      obtain ⟨r_C, hr_C⟩ : ∃ r_C : Finset (Fin n) → Fin n, ∀ C ∈ P, r_C C ∈ C ∧ adj r (r_C C) := by
        have h_exists_r_C : ∀ C ∈ P, ∃ w ∈ C, adj r w := by
          intro C hC
          obtain ⟨w, hw⟩ : ∃ w ∈ C, reachIn adj K r w := by
            exact Exists.elim (hP.2.1 C hC)
              fun w hw => ⟨w, hw, hconn w (Finset.mem_of_mem_erase (hP.1 C hC hw))⟩
          have := exists_first_neighbor hw.2 (by grind +revert)
          grind
        exact ⟨fun C => if hC : C ∈ P then Classical.choose (h_exists_r_C C hC) else r,
          fun C hC => by simpa [hC] using Classical.choose_spec (h_exists_r_C C hC)⟩
      -- For each component $C \in P$, apply the induction hypothesis to obtain a weighting $y_C$.
      obtain ⟨y_C, hy_C⟩ : ∃ y_C : Finset (Fin n) → (Fin n → ℝ), (∀ C ∈ P,
          (∀ i, 0 ≤ y_C C i) ∧
          (∀ i ∉ C, y_C C i = 0) ∧
          y_C C (r_C C) = C.card / (C.card + 1) ∧
          (C.card : ℝ) / (C.card + 1)
            ≤ 2 * y_C C (r_C C) - 2 * ∑ i ∈ C, y_C C i ^ 2
              + ∑ i ∈ C, ∑ j ∈ C, (if adj i j then y_C C i * y_C C j else 0)) := by
        have h_ind_step : ∀ C ∈ P, ∃ y_C : Fin n → ℝ,
            (∀ i, 0 ≤ y_C i) ∧
            (∀ i ∉ C, y_C i = 0) ∧
            y_C (r_C C) = C.card / (C.card + 1) ∧
            (C.card : ℝ) / (C.card + 1)
              ≤ 2 * y_C (r_C C) - 2 * ∑ i ∈ C, y_C i ^ 2
                + ∑ i ∈ C, ∑ j ∈ C, (if adj i j then y_C i * y_C j else 0) := by
          intros C hC
          apply ih (C.card) (by
          exact lt_of_le_of_lt (Finset.card_le_card (hP.1 C hC)) (by rw [Finset.card_erase_of_mem hr, hK] ; omega)) C rfl (r_C C) (hr_C C hC).left (by
          intro w hw
          have h_reach : reachIn adj (K.erase r) (r_C C) w := by
            grind +splitIndPred
          have h_reach_C : reachIn adj C (r_C C) w := by
            convert reachIn_confine h_reach using 1;
            grind +locals
          exact h_reach_C)
        choose! y_C hy_C using h_ind_step;
        use y_C;
      -- Define the weighting $y$ for the entire set $K$.
      use fun i => if i = r then (N : ℝ) / (N + 1)
        else ∑ C ∈ P, (if i ∈ C then ((C.card + 1) / (N + 1)) * y_C C i else 0)
      refine' ⟨ _, _, _, _ ⟩
      · simp +zetaDelta at *
        intro i
        split_ifs
        · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
        · exact Finset.sum_nonneg fun C hC => by
            split_ifs
            · exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (hy_C C hC |>.1 i)
            · exact le_rfl
      · simp +contextual
        intro i hi
        split_ifs
        <;> simp_all [Finset.subset_iff]
        exact Finset.sum_eq_zero fun C hC => if_neg fun hiC => hi <| hP.1 C hC hiC |>.2
      · simp +decide
      · convert energy_scalar N (by linarith) P (fun C => C.card) (fun C => ∑ i ∈ C, y_C C i ^ 2)
          (fun C => ∑ i ∈ C, ∑ j ∈ C, if adj i j then y_C C i * y_C C j else 0)
          (fun C => ∑ i ∈ C, if adj r i then y_C C i else 0) _ _ _ using 1
        · congr! 1
          · convert combined_sq_sum P (K.erase r) K r (N / (N + 1))
              (fun C i => (C.card + 1 : ℝ) / (N + 1) * y_C C i) _ _ _ _ _ using 1
            rotate_right
            use fun i => if i = r then N / (N + 1)
              else ∑ C ∈ P, if i ∈ C then (C.card + 1 : ℝ) / (N + 1) * y_C C i else 0
            · simp [Finset.sum_ite, Finset.filter_ne',
                Finset.filter_eq', Finset.mul_sum _ _ _, mul_pow]
            · simp [hr]
            · rw [Finset.insert_erase hr]
            · exact hP.2.2.1
            · exact hP.2.2.2.1
          · rw [combined_cross_sum adj hsymm hirr P (K.erase r) K r (N / (N + 1))
              (fun C i => (C.card + 1 : ℝ) / (N + 1) * y_C C i)]
            any_goals tauto
            · congr!
              <;> simp [Finset.mul_sum]
              ring_nf
            · simp [hr]
            · rw [Finset.insert_erase hr]
            · exact hP.2.2.2.1
            · exact fun C hC i hi => mul_eq_zero_of_right _ (hy_C C hC |>.2.1 i hi)
        · have h_sum_card : ∑ C ∈ P, C.card = (K.erase r).card := by
            rw [hP.2.2.1, Finset.card_biUnion]
            · rfl
            · exact fun x hx y hy hxy => hP.2.2.2.1 x hx y hy hxy
          rw [← Nat.cast_sum, h_sum_card, Finset.card_erase_of_mem hr, hK]
          rw [Nat.cast_pred (by linarith)]
        · grind
        · intro C hC
          specialize hy_C C hC
          specialize hr_C C hC
          simp [Finset.sum_ite]
          refine' le_trans _ (Finset.single_le_sum (fun x _ => hy_C.1 x)
            (Finset.mem_filter.mpr ⟨ hr_C.1, hr_C.2 ⟩))
          aesop
  exact h_ind_step _ _ rfl _ hr hconn
