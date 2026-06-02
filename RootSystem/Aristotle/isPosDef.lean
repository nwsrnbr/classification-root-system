import Mathlib

open Matrix Finset

variable {n : ℕ}

variable {ι E F : Type*} [Nonempty ι] [Finite ι] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
  (Φ : RootPairing ι ℝ E F) [Φ.IsCrystallographic] {b : Φ.Base} (h_irred : Φ.IsIrreducible)

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

lemma symmMatrix_isHermitian (C : Matrix (Fin n) (Fin n) ℤ) :
    (SymmMatrix C).IsHermitian := by
  ext i j; by_cases hij : i = j <;> simp +decide [hij, SymmMatrix]; ring; aesop

section RootFormLemmas

variable {ι' R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι' R M N) [Fintype ι']

/-- 2 * RootForm(root i, root j) = pairing(i,j) * RootForm(root j, root j) -/
lemma two_mul_rootForm_root_root_eq (i j : ι') :
    2 * (P.RootForm (P.root i)) (P.root j) =
    P.pairing i j * (P.RootForm (P.root j)) (P.root j) := by
  have h1 := P.rootForm_self_smul_coroot j
  apply_fun fun x => P.toLinearMap (P.root i) x at h1
  convert h1.symm using 1 <;> simp +decide [mul_comm, two_smul]
  simp +decide [← two_mul, P.rootForm_apply_apply]

end RootFormLemmas

/-- For a root system over ℝ, RootForm is positive definite: RootForm(x, x) > 0 for x ≠ 0 -/
lemma rootForm_pos_of_ne_zero {ι' : Type*} [Fintype ι'] {P : RootPairing ι' ℝ E F}
    [P.IsRootSystem] (x : E) (hx : x ≠ 0) :
    0 < (P.RootForm x) x := by
  by_cases h_zero : (P.RootForm x) x = 0
  · convert P.rootForm_anisotropic
    simp +decide [QuadraticMap.Anisotropic]
    grind
  · exact lt_of_le_of_ne (RootPairing.zero_le_rootForm P x) (Ne.symm h_zero)

/-- The Gram matrix of linearly independent vectors under a positive definite bilinear form
    is positive definite. -/
lemma gramMatrix_posDef {m : ℕ} (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB_sym : LinearMap.IsSymm B)
    (hB_pos : ∀ x : E, x ≠ 0 → 0 < (B x) x)
    (v : Fin m → E)
    (hv : LinearIndependent ℝ v) :
    (Matrix.of fun i j => (B (v i)) (v j)).PosDef := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j; simp [Matrix.of_apply]; exact hB_sym.eq (v j) (v i)
  · have hw_ne_zero : ∑ i ∈ x.support, x i • v i ≠ 0 := by
      exact Ne.symm (Ne.intro fun a => hx (hv (id (Eq.symm a))))
    convert hB_pos _ hw_ne_zero using 1
    simp +decide [Finsupp.sum, map_sum, map_smul]
    simp +decide only [mul_comm, Finset.mul_sum _ _ _]
    rw [Finset.sum_comm]

/-- For c ≤ 0, c * √r = -√(c² * r) for r ≥ 0. -/
lemma neg_mul_sqrt_eq {c r : ℝ} (hc : c ≤ 0) (_hr : 0 ≤ r) :
    c * Real.sqrt r = -Real.sqrt (c ^ 2 * r) := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonpos hc, mul_comm]; ring

/-- Key identity: for p, q ≤ 0 real numbers with p * c = q * a (where a, c > 0),
    p * √(c / a) = -√(p * q). -/
lemma pairing_sqrt_ratio_eq {p q a c : ℝ} (hp : p ≤ 0) (_hq : q ≤ 0)
    (ha : 0 < a) (_hc : 0 < c) (hsym : p * c = q * a) :
    p * Real.sqrt (c / a) = -Real.sqrt (p * q) := by
  by_cases hpq : p = 0
  · aesop
  · rw [show p * q = p ^ 2 * (c / a) by
      rw [eq_comm, mul_div_assoc', div_eq_iff] <;> cases lt_or_gt_of_ne hpq <;> nlinarith,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonpos hp]; ring

/-
Positive scalar multiples of linearly independent vectors remain linearly independent.
-/
lemma linearIndependent_smul_of_pos {m : ℕ} {M' : Type*} [AddCommGroup M'] [Module ℝ M']
    (f : Fin m → ℝ) (hf : ∀ k, 0 < f k)
    (v : Fin m → M') (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun k => f k • v k) := by
  convert hv.units_smul fun k => Units.mk0 _ ( ne_of_gt ( hf k ) )

/-
For a > 0, √2/√a * (√2/√a * a) = 2.
-/
lemma sqrt_div_sq_mul {a : ℝ} (ha : 0 < a) :
    Real.sqrt 2 / Real.sqrt a * (Real.sqrt 2 / Real.sqrt a * a) = 2 := by
  grind

/-
The off-diagonal entry of the SymmMatrix equals the normalized RootForm entry.
-/
lemma normalized_rootForm_off_diag {ι' : Type*} [Fintype ι']
    {P : RootPairing ι' ℝ E F} [P.IsRootSystem] [P.IsCrystallographic]
    {b' : P.Base} (i j : ι') (hij : i ≠ j)
    (hi : i ∈ b'.support) (hj : j ∈ b'.support) :
    let Gii := (P.RootForm (P.root i)) (P.root i)
    let Gjj := (P.RootForm (P.root j)) (P.root j)
    Real.sqrt (2 / Gii) * Real.sqrt (2 / Gjj) * (P.RootForm (P.root i)) (P.root j) =
    -(Real.sqrt (↑(P.pairingIn ℤ i j * P.pairingIn ℤ j i))) := by
  have h_symm : P.pairing i j * (P.RootForm (P.root j)) (P.root j) = P.pairing j i * (P.RootForm (P.root i)) (P.root i) := by
    have := two_mul_rootForm_root_root_eq P i j;
    have := two_mul_rootForm_root_root_eq P j i;
    simp_all +decide [ RootPairing.RootForm ];
    grind +revert;
  have h_neg : P.pairing i j ≤ 0 ∧ P.pairing j i ≤ 0 := by
    have := b'.pairingIn_le_zero_of_ne hij;
    have := b'.pairingIn_le_zero_of_ne hij.symm;
    have h_cast : (algebraMap ℤ ℝ) (P.pairingIn ℤ i j) = P.pairing i j ∧ (algebraMap ℤ ℝ) (P.pairingIn ℤ j i) = P.pairing j i := by
      exact ⟨ P.algebraMap_pairingIn ℤ i j, P.algebraMap_pairingIn ℤ j i ⟩;
    exact ⟨ h_cast.1 ▸ Int.cast_nonpos.mpr ( by solve_by_elim ), h_cast.2 ▸ Int.cast_nonpos.mpr ( by solve_by_elim ) ⟩;
  have h_pos : 0 < (P.RootForm (P.root i)) (P.root i) ∧ 0 < (P.RootForm (P.root j)) (P.root j) := by
    have h_pos : ∀ x : E, x ≠ 0 → 0 < (P.RootForm x) x := by
      apply rootForm_pos_of_ne_zero;
    exact ⟨ h_pos _ ( P.ne_zero _ ), h_pos _ ( P.ne_zero _ ) ⟩;
  have h_eq : (P.RootForm (P.root i)) (P.root j) = P.pairing i j * (P.RootForm (P.root j)) (P.root j) / 2 := by
    linarith [ two_mul_rootForm_root_root_eq P i j ];
  convert pairing_sqrt_ratio_eq h_neg.1 h_neg.2 h_pos.1 h_pos.2 h_symm using 1;
  · norm_num [ mul_assoc, mul_comm, mul_left_comm, h_pos.1.le, h_pos.2.le ];
    grind;
  · simp +decide [ RootPairing.pairingIn ];
    grind

include h_irred in
lemma isPosDef :
    let n := Fintype.card b.support
    let e : b.support ≃ Fin n := Fintype.equivFin _
    (SymmMatrix (b.cartanMatrix.reindex e e)).PosDef := by
  let nn := Fintype.card b.support
  let e : b.support ≃ Fin nn := Fintype.equivFin _
  let C := (b.cartanMatrix.reindex e e)
  show (SymmMatrix C).PosDef
  haveI : Fintype ι := Fintype.ofFinite ι
  letI : Φ.IsIrreducible := h_irred
  haveI : Φ.IsRootSystem := inferInstance
  -- Define normalized root vectors
  let root' : Fin nn → E := fun k => Φ.root (↑(e.symm k) : ι)
  let d : Fin nn → ℝ := fun k => Real.sqrt (2 / (Φ.RootForm (root' k)) (root' k))
  let v : Fin nn → E := fun k => d k • root' k
  -- Show the Gram matrix of v under RootForm equals SymmMatrix C
  suffices h : ∀ i j, (Φ.RootForm (v i)) (v j) = SymmMatrix C i j by
    have hGram : (Matrix.of fun i j => (Φ.RootForm (v i)) (v j)) = SymmMatrix C := by
      ext i j; exact h i j
    rw [← hGram]
    exact gramMatrix_posDef Φ.RootForm (RootPairing.rootForm_symmetric Φ)
      rootForm_pos_of_ne_zero v
      (linearIndependent_smul_of_pos d (fun k => by
        apply Real.sqrt_pos_of_pos
        exact div_pos two_pos (rootForm_pos_of_ne_zero _ (Φ.ne_zero _)))
        root' (by
        -- root' is linearly independent (it's the base roots via an equivalence)
        have h_lin_indep : LinearIndependent ℝ (fun i : b.support => Φ.root i) := by
          convert b.linearIndepOn_root;
        convert h_lin_indep.comp _ e.symm.injective using 1))
  intro i j
  simp only [v, d]
  by_cases hij : i = j
  · -- Diagonal case
    subst hij
    simp [SymmMatrix, Matrix.of_apply]
    exact sqrt_div_sq_mul (rootForm_pos_of_ne_zero _ (Φ.ne_zero _))
  · -- Off-diagonal case
    simp only [SymmMatrix, Matrix.of_apply, hij, ite_false]
    -- Need: RootForm(√(2/G_ii) • root_i, √(2/G_jj) • root_j) = -√(C_ij * C_ji)
    -- The LHS, by bilinearity, = √(2/G_ii) * √(2/G_jj) * RootForm(root_i, root_j)
    -- By normalized_rootForm_off_diag, this equals -√(pairing(i,j) * pairing(j,i))
    -- And C_ij = pairing_ℤ for the reindexed Cartan matrix
    have := @normalized_rootForm_off_diag;
    convert this ( e.symm i : ι ) ( e.symm j : ι ) ( by simpa [ e.injective.eq_iff ] using hij ) ( e.symm i |>.2 ) ( e.symm j |>.2 ) using 1;
    · simp +decide [ root', LinearMap.smul_apply ];
      ring;
    · simp +decide [ C, Matrix.reindex_apply ];
      rfl