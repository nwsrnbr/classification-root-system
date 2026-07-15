import RootSystem.Aristotle.Core

variable {n : ℕ}

open Matrix CartanMatrix

/-- If there is a path from `v` to `v'` avoiding `u` (`reachExcl C u v v'`), while
`u` is adjacent to both `v` and `v'` and `v ≠ v'`, then closing the path through `u`
yields a genuine cycle, contradicting positive-definiteness via `no_cycle`. -/
lemma no_posDef_of_branch_path (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (u v v' : Fin n) (hvv : v ≠ v')
    (hv : Gadj C u v) (hv' : Gadj C u v') (hpath : reachExcl C u v v') :
    ¬ (SymmMatrix C).PosDef := by
  -- If $u$ and $v$ are adjacent, then by `reachExcl_ne_u`, $v \ne u$.
  have hv_ne_u : v ≠ u := by
    exact hv.1.symm
  have hv'_ne_u : v' ≠ u := by
    exact hv'.1.symm;
  obtain ⟨s, hs⟩ : ∃ s : List (Fin n), s.head? = some v ∧ s.getLast? = some v' ∧ s.Nodup ∧ List.IsChain (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u) s := by
    obtain ⟨p, hp⟩ : ∃ p : SimpleGraph.Walk (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) v v', p.IsPath := by
      obtain ⟨p, hp⟩ : ∃ p : SimpleGraph.Walk (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) v v', True := by
        have h_reachable : SimpleGraph.Reachable (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) v v' := by
          have h_path : ∀ {i j : Fin n}, reachExcl C u i j → SimpleGraph.Reachable (SimpleGraph.fromRel (fun i j => Gadj C i j ∧ i ≠ u ∧ j ≠ u)) i j := by
            intro i j hij; induction hij; aesop;
            rename_i k hk₁ hk₂ hk₃;
            exact hk₃.trans ( SimpleGraph.Adj.reachable <| by unfold adjExcl at hk₂; unfold Gadj; aesop );
          exact h_path hpath;
        exact ⟨ h_reachable.some, trivial ⟩;
      exact ⟨ p.toPath, p.toPath.isPath ⟩;
    refine' ⟨ p.support, _, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    · cases p <;> aesop;
    · cases p <;> simp_all +decide [ List.getLast? ];
    · simp_all +decide [ List.isChain_iff_get ];
      intro i; have := p.adj_getVert_succ ( show i.val < p.length from by
                                              exact lt_of_lt_of_le i.2 ( Nat.sub_le_of_le_add <| by simp +arith +decide ) ) ; simp_all +decide [ SimpleGraph.fromRel_adj ] ;
      grind +suggestions;
  -- Put `L := u :: s`. Then `L.length = s.length + 1 ≥ 3`, and `L.Nodup` by `List.nodup_cons.mpr ⟨hnotu, hs.2.2.1⟩`.
  set L : List (Fin n) := u :: s
  have hL_len : 3 ≤ L.length := by
    rcases s with ( _ | ⟨ x, _ | ⟨ y, s ⟩ ⟩ ) <;> simp_all +decide; all_goals grind
  have hL_nodup : L.Nodup := by
    simp +zetaDelta at *;
    have := hs.2.2.2; simp_all +decide [ List.isChain_iff_get ] ;
    intro hu; rcases List.mem_iff_get.mp hu with ⟨ i, hi ⟩ ; rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide ;
    · cases s <;> aesop;
    · exact hs.2.2.2 ⟨ i, Nat.lt_pred_iff.mpr ‹_› ⟩ |>.2.2 hi
  have hL_cycle : ∀ i : Fin L.length, C (L.get i) (L.get ⟨(i.val + 1) % L.length, Nat.mod_lt _ (by omega)⟩) ≠ 0 := by
    intro i
    by_cases hi : i.val = 0 ∨ i.val = L.length - 1;
    · rcases hi with ( hi | hi ) <;> simp_all +decide;
      · rcases s with ( _ | ⟨ x, _ | ⟨ y, s ⟩ ⟩ ) <;> simp_all +decide [ Gadj ];
        · grind;
        · aesop;
      · simp +zetaDelta at *;
        convert hv'.2 using 1;
        grind +splitIndPred;
    · have := List.isChain_iff_get.mp hs.2.2.2;
      rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide;
      have := this ⟨ i, by
        grind ⟩
      generalize_proofs at *;
      simp +zetaDelta at *;
      simp_all +decide [ Nat.mod_eq_of_lt ( by linarith : i + 1 + 1 < s.length + 1 ), Gadj ];
  exact no_cycle_list C hGCM L hL_nodup hL_len hL_cycle

/-- **Distinctness of branches.**  At a degree-3 vertex of a positive-definite
Dynkin graph, the three branches are pairwise disjoint (otherwise there is a cycle
through `u`, contradicting acyclicity of positive-definite Dynkin diagrams). -/
lemma branches_disjoint (C : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGeneralizedCartanMatrix C)
    (hP : (SymmMatrix C).PosDef) (u : Fin n) (v v' : Fin n) (hvv : v ≠ v')
    (hv : v ∈ neighborSet C u) (hv' : v' ∈ neighborSet C u) :
    Disjoint (branchFinset C u v) (branchFinset C u v') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  have hadjsymm : Symmetric (adjExcl C u) := by
    rintro a b ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h3, h2, fun h => h4 ((hGCM.vanish_symm b a).mp h)⟩
  have hreach_w : reachExcl C u v w := (mem_branchFinset C u v w).mp hw
  have hreach_w' : reachExcl C u v' w := (mem_branchFinset C u v' w).mp hw'
  have hpath : reachExcl C u v v' :=
    hreach_w.trans (Relation.ReflTransGen.symmetric hadjsymm hreach_w')
  exact no_posDef_of_branch_path C hGCM u v v' hvv
    ((neighbor_iff_Gadj C u v).mp hv) ((neighbor_iff_Gadj C u v').mp hv') hpath hP

/-- The analytic core (Schur complement positivity): for a degree-3 vertex of a
positive-definite Dynkin graph, the sum of `aᵢ/(aᵢ+1)` over the three branches is
strictly below `2`. -/
lemma schur_ineq (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    (branchSize C u v₁ : ℝ) / ((branchSize C u v₁ : ℝ) + 1) +
    (branchSize C u v₂ : ℝ) / ((branchSize C u v₂ : ℝ) + 1) +
    (branchSize C u v₃ : ℝ) / ((branchSize C u v₃ : ℝ) + 1) < 2 := by
  by_contra hcon
  push_neg at hcon
  have htrip := neighborSet_eq_triple C u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist
  have hv₁u : v₁ ≠ u := ((neighbor_iff_Gadj C u v₁).mp hv₁).1.symm
  have hv₂u : v₂ ≠ u := ((neighbor_iff_Gadj C u v₂).mp hv₂).1.symm
  have hv₃u : v₃ ≠ u := ((neighbor_iff_Gadj C u v₃).mp hv₃).1.symm
  have hu1 := u_notMem_branch C u v₁ hv₁u
  have hu2 := u_notMem_branch C u v₂ hv₂u
  have hu3 := u_notMem_branch C u v₃ hv₃u
  obtain ⟨y₁, hy₁nn, hy₁s, hy₁E⟩ := branch_marking C hGCM u v₁
  obtain ⟨y₂, hy₂nn, hy₂s, hy₂E⟩ := branch_marking C hGCM u v₂
  obtain ⟨y₃, hy₃nn, hy₃s, hy₃E⟩ := branch_marking C hGCM u v₃
  have hd12 := branches_disjoint C hGCM hP u v₁ v₂ hdist.1 hv₁ hv₂
  have hd13 := branches_disjoint C hGCM hP u v₁ v₃ hdist.2.1 hv₁ hv₃
  have hd23 := branches_disjoint C hGCM hP u v₂ v₃ hdist.2.2 hv₂ hv₃
  have hxnn : ∀ i, 0 ≤ (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) i := by
    intro i; simp only; split_ifs
    · norm_num
    · exact add_nonneg (add_nonneg (hy₁nn i) (hy₂nn i)) (hy₃nn i)
  have hxne : (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) ≠ 0 := by
    intro h
    have : (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) u = 0 := by rw [h]; rfl
    simp at this
  have hpos := hP.dotProduct_mulVec_pos hxne
  have hle := form_le_Gadj C hGCM (fun i => if i = u then (1:ℝ) else y₁ i + y₂ i + y₃ i) hxnn
  have hsq := assembly_sq C u v₁ v₂ v₃ y₁ y₂ y₃ hu1 hu2 hu3 hy₁s hy₂s hy₃s hd12 hd13 hd23
  have hcr := assembly_cross C hGCM u v₁ v₂ v₃ y₁ y₂ y₃ htrip hu1 hu2 hu3 hy₁s hy₂s hy₃s
    hd12 hd13 hd23
  simp only at hle
  rw [hsq, hcr] at hle
  linarith [hpos, hle, hy₁E, hy₂E, hy₃E, hcon]

theorem branciSize_inequality (C : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGeneralizedCartanMatrix C) (hP : (SymmMatrix C).PosDef)
    (u : Fin n) (hu : degree C u = 3)
    (v₁ v₂ v₃ : Fin n)
    (hv₁ : v₁ ∈ neighborSet C u) (hv₂ : v₂ ∈ neighborSet C u)
    (hv₃ : v₃ ∈ neighborSet C u)
    (hdist : v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) :
    (1 : ℝ) / ((branchSize C u v₁ : ℝ) + 1) +
    (1 : ℝ) / ((branchSize C u v₂ : ℝ) + 1) +
    (1 : ℝ) / ((branchSize C u v₃ : ℝ) + 1) > 1 := by
  have key := schur_ineq C hGCM hP u hu v₁ v₂ v₃ hv₁ hv₂ hv₃ hdist
  set a : ℝ := (branchSize C u v₁ : ℝ) with ha
  set b : ℝ := (branchSize C u v₂ : ℝ) with hb
  set c : ℝ := (branchSize C u v₃ : ℝ) with hc
  have ha1 : (a:ℝ) + 1 ≠ 0 := by positivity
  have hb1 : (b:ℝ) + 1 ≠ 0 := by positivity
  have hc1 : (c:ℝ) + 1 ≠ 0 := by positivity
  have e₁ : a / (a + 1) = 1 - 1 / (a + 1) := by field_simp; ring
  have e₂ : b / (b + 1) = 1 - 1 / (b + 1) := by field_simp; ring
  have e₃ : c / (c + 1) = 1 - 1 / (c + 1) := by field_simp; ring
  rw [e₁, e₂, e₃] at key
  linarith
