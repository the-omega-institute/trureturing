import GRH.Lib.ClassField.GreenbergWiles.ExtendCharacter
import GRH.Lib.ClassField.GaloisCohomology.SylowReduction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Galois cohomology in degrees ≤ 2, covering Shapiro, Hilbert 90, Kummer, symbols
and the Herbrand quotient. Only explicit continuous cocycles are used, and Shapiro's lemma appears
only as injectivity. Corestriction is summation on functions on a coset space, and Tate's lemma on
the Herbrand quotient is an index formula for a group of prime order. Source: J.-P. Serre, Galois
Cohomology (1997); Neukirch–Schmidt–Wingberg, Cohomology of Number Fields (2nd ed. 2008), Ch. I, VI;
Atiyah–Wall, Cohomology of groups, in Cassels–Fröhlich (1967), IV §8.

Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles (known
result; see Lib.ClassField.LocalDuality.CrystallineDuality).

This file: Index of n-th powers in the multiplicative group of a local field. Tate's index formula
for norms on stable subgroups in prime-degree Galois extensions. Classes split by a cyclic extension
are symbols; symbols vanish exactly on norms. -/

open Algebra IsLocalRing Quotient DiscreteModule Fint Group Ideal IsGalois LinearMap Module
  MulSemiringAction Polynomial QuotientGroup Submodule DiscreteUnits Valuation groupCohomology
  Ideal.Quotient Mathlib.Tactic.LinearCombination

attribute [-simp] map_smul

attribute [local simp] NeZero.ne pos_iff div_sub_one cokerKerIndex valuationVia

/-- For a local field L with integers O, l ≠ 0 and a group Y ≅ L^×, the quotient #(Y/lY) / #Y[l]
is non-zero and equals l·#(O/l). -/
lemma cokerKerIndex_local_units {Γ L Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field L] [Field Ω]
  [Algebra L Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} (h : IsLocalGalois Γ L A) (l : ℕ)
  [NeZero l] {Y} [AddCommGroup Y] (y : Y ≃+ Additive Lˣ) : cokerKerIndex (l : End ℤ Y) ≠ 0 ∧
  cokerKerIndex (l : End ℤ Y) = l * Nat.card (_ ⧸ Ideal.span {(l : valRingBelow L A)}) := by
  obtain ⟨⟨π, hπ⟩, ⟨⟩⟩ := h.5.exists_irreducible, _root_.id h, (algebraMap L Ω).charZero
  have F x e := finite_quotient_iff.2 ((exists_maximalIdeal_pow_eq_of_principal (valRingBelow L A)
    inferInstance (Ideal.span {x}) (by simpa)).imp fun _ ↦ Eq.ge)
  obtain ⟨c⟩ := mul_ne_zero (NeZero.ne ↑l) hπ.ne_zero,
    (isUniformiser_iff_irreducible.2 ⟨_, hπ⟩).val_lt_one, hπ.ne_zero
  let w := Units.mk0 (valuationVia L A (l * π)) (by simpa)
  obtain ⟨k⟩ := (by simpa [w] : w < A l), F l (by simp), F _ c
  let r := (Units.map (Ideal.Quotient.mk (Ideal.span {l * π})).1).toAdditive.toIntLinearMap
  choose d hd using fun a : r.ker ↦
    (mk_span_eq_iff_dvd_sub.1 congr($(a.2).1)).imp fun _ ↦ eq_add_of_sub_eq'
  let j x : r.ker := ⟨.ofMul (isUnit_of_mem_nonunits_one_sub_self (1 + l * π * x) (by
    simp [hπ.1])).unit, by ext; simp [r]⟩
  rw [cokerKerIndex_natCast_eq_of_ne_zero (y.trans (.symm (.ofBijective ((Units.map (algebraMap _
    L).1).toAdditive.coprod (zmultiplesHom _ (.ofMul (.mk0 π (by simpa))))) ⟨.of_ker _ fun ⟨u,
    n⟩ e ↦ by simp_all [Units.ext_iff, (by simpa [← (valRingBelow L A).valuation_eq_one_iff, hπ.1,
    zpow_eq_one_iff_right₀] using congr(valRingBelow L A ($e).toMul.1) : n = 0)], fun a ↦
    have ⟨n, u, _⟩ := h.5.exists_units_eq_smul_zpow_of_irreducible hπ a.toMul.ne_zero
    ⟨(u, n), by aesop⟩⟩))).toIntLinearEquiv.1 (by simp), cokerKerIndex_mul_of_exact _ _
    inr_injective .inr_fst fst_surjective cokerKerIndex_eq_pow_finrank.1,
    cokerKerIndex_eq_pow_finrank.2, ← cokerKerIndex_natCast_eq_of_ne_zero r.ker.subtype
    (by simpa using! r.toAddMonoidHom.ker.index_ne_zero_of_finite), cokerKerIndex, ker_eq_bot'.2
    fun (a : r.ker) e ↦ by ext; exact (algebraMap ..).injective (eq_of_pow_eq_one_of_val_sub_lt (by
    simpa [← map_pow] using congr($e.1.toMul.1.1)) (by simp) (k.trans_le' (by simpa [hd, w] using
    (mul_le_of_le_one_right' (d a).2)))), Nat.card_congr (Function.Exact.linearEquivOfSurjective
    (g := (AddMonoidHom.mk' (Ideal.Quotient.mk (Ideal.span {↑l}) ∘ d)
    fun a b ↦ mk_span_eq_iff_dvd_sub.2 ⟨d a * d b * π, mul_left_cancel₀ c (by
    grind -linarith [show _ * _ = _ from hd (a + b)])⟩).toIntLinearMap) (.of_comp_of_mem_range (by
    ext; simpa using mul_eq_zero_of_left (mk_singleton_self _) _) fun a e ↦ ?_) (Quot.ind fun x ↦
    ⟨_, congrArg _ (by simpa [j, c] using (hd (j x)).symm)⟩)).toEquiv]
  simp
  obtain ⟨z, E, s⟩ : ∃ z, algebraMap L Ω a.1.toMul.1 = z ^ l ∧ A (z - 1) ≤ w
  · by_contra! N
    have := by simpa [hd] using N 1
    apply (dvd_iff_valuationVia_le.1 ((eq_zero_iff_dvd ..).1 e)).not_gt
    simpa [w, derivative_pow, field, *] using ((h.2.1 (C (algebraMap L Ω a.1.toMul.1) -
      X ^ l)).eval_derivative_div_eval_of_ne_zero (x := 1) (by simp [*]) ▸
      (A.valuation.ltAddSubgroup w⁻¹).multiset_sum_mem _ (by simp_all [inv_strictAnti₀,
      ↓Multiset.forall_mem_map_iff, map_sub_swap]) :)
  obtain ⟨x, rfl⟩ := h.1.1.3.1 z fun g ↦ eq_of_div_eq_one (eq_of_pow_eq_one_of_val_sub_lt (by
    simp [div_pow, ← smul_pow', ← E]) (by simp) (((map_sub_le _ (decompGroup.val_smul (h.4 g) _ ▸ s)
    s).trans_lt k).trans_eq' (by simp [map_eq_of_sub_lt _ (s.trans_lt (k.trans_le (by simp))),
    ← A.valuation.zero_iff, smul_sub])))
  use j ⟨(x - 1) / (l * π), by simp_all [w, field]⟩
  ext; simp_all [j, mul_div_cancel₀, ← map_pow, -hd]

/-- Let L/K be Galois of prime degree l, U ⊂ L^× Galois-stable, V = U ∩ K^×, and gz/z ∈ U for
all g only if z ∈ K^×U. With q_A = #(A/lA)/#A[l] and q_V ≠ 0, [V : N U]^{l−1} q_U = q_V^l. -/
lemma tate_index_formula_norm {K L} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] l (hL : finrank K L = l) [Fact l.Prime] (U : Subgroup Lˣ) (V : Subgroup Kˣ)
  (hV : V = U.comap (Units.map (algebraMap K L))) (hU : ∀ g : Gal(L/K), ∀ y ∈ U, g • y ∈ U)
  (h : ∀ z, (∀ g : Gal(L/K), g • z / z ∈ U) → ∃ x : Kˣ, x.map (algebraMap K L) / z ∈ U) (iV :
  cokerKerIndex (l : End ℤ (Additive V)) ≠ 0) : (U.map (Units.map (Algebra.norm K))).relIndex V ^ (l
  - 1) * cokerKerIndex (l : End ℤ (Additive U)) = cokerKerIndex (l : End ℤ (Additive V)) ^ l := by
  subst_vars; have i@⟨g, hg⟩ := isCyclic_of_prime_card (card_aut_eq_finrank K L)
  let σ : _ →* End ℤ (Additive U) := unitsRep.subrepresentation U.toAddSubgroup.toIntSubmodule hU
  rw [Subgroup.relIndex, ← MonoidHom.domRestrict_range, MonoidHom.subgroupOf_range_eq_of_le _ ?n]
  use Tate.index_formula (MonoidHom.codRestrict _ (U.comap _) (?n ⟨·,
    rfl⟩)).toAdditive.toIntLinearMap (MonoidHom.subgroupComap ..).toAdditive.toIntLinearMap (σ g) iV
    (by simp [← card_aut_eq_finrank, ← map_pow]) (.restrictPreimage _ (Units.map_injective
    (by aesop_cat))) (fun y ↦ sub_eq_zero.trans ⟨fun a ↦
    (Set.range_restrictPreimage ..).ge (((ofBase_bijective _).2 ⟨y.1, fun k ↦
    Units.ext (smul_eq_self_of_mem_zpowers (hg k) congr($a.1.1))⟩).imp fun _ ↦ Subtype.ext_iff.1),
    (·.choose_spec ▸ by ext; apply g.commutes)⟩) (.of_comp_of_mem_range (by ext; simp [field]; apply
    norm_eq_of_algEquiv) fun y hy ↦ (exists_div_of_norm_eq_one hg (x := y.1) congr($hy.1)).rec fun z
    e ↦ ⟨.ofMul ⟨_, (h z (hg · |> mem_powers_iff_mem_zpowers.2 |>.rec fun n E ↦
    E ▸ n.rec (by simp) fun _ I ↦ Eq.subst (by ext; simp [← e, pow_succ', field]) (div_mem (hU g _
    I) y.2))).choose_spec⟩, by ext; erw [← e, Units.val_mul, Units.coe_smul, Units.val_mul]; simp
    [field]⟩) (by ext; apply Algebra.norm_algebraMap)
  simp [LE.le]; intros
  convert (∏ g, ⟨_, hU g _ ‹_›⟩ : U).2; ext; simp [norm_eq_prod_automorphisms]

attribute [-simp] LinearMap.map_smul_of_tower Pi.smul_apply one_apply zsmul_eq_mul

variable {Γ K Ω L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] [Field L] [Algebra K L] [Algebra L Ω]

lemma IsProGalois.of_fixingSubgroup_eq [IsScalarTower K L Ω] {U} (h :
  fixingSubgroup Γ (.range (algebraMap L Ω)) = U) [@IsClosed Γ _ U] :
  IsProGalois U L Ω := { tower_top_of_isGalois K .., (inferInstance : IsProGalois ..) with
    commutes.1 := by simp +contextual [Algebra.smul_def, ← h, mem_fixingSubgroup_iff]
    isInvariant.1 := h ▸ (fixedFieldOf_fixingSubgroup (algHom ..).fieldRange).le }

attribute [local simp] DiscreteModule.sum Finset.smul_sum mul_eq_one_iff_inv_eq smul_sub sub_smul

/-- Let χ : Γ → ℚ/ℤ have open kernel U. A class in H²(Γ, Ω^×) restricts to zero on U exactly
when it is a symbol (χ, w), w ∈ K^×; and (χ, w) = 0 exactly when w is a norm from the fixed
field of U.

Known result: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient. -/
lemma QZChar.cyclicClass_spec χ : let U := OpenSubgroup.mk _ (isOpen_ker χ); (∀ x,
    (unitsModule Γ).resH2 U x = 0 ↔ ∃ w : Kˣ, x = cyclicClass _ χ (ofBase Γ Ω (.ofMul w))) ∧ ∀ w :
    (unitsModule Γ).H0, cyclicClass _ χ w = 0 ↔ ∃ y, corestrictH0 U y =
    w.1 := by intro U; refine have := U.1.quotient_finite_of_isOpen U.2
  let f q := (kerLift (toHom χ) q).toAdd
  (Finite.exists_max (QZ.fracRep ∘ f)).elim fun γ hγ ↦ let c p q := QZ.carry (f p) (f q)
    have E q : c q γ = 1 - ite (q = 1) 1 0 :=
      sub_eq_zero.1 (Int.abs_lt_one_iff.1 (by qify [c]; grind
      [mul_eq_right, QZ.fracRep, Equiv.injective, kerLift_injective, toAdd_mul, hγ (q * γ)]))
    let M := unitsModule Γ; let D := funLeft ℤ M (· * γ) - 1
      have H f := (hilbert90_unitsRep (M.shapiroZ1 U f)).elim (shapiro_H1 U f)
      have j g : χ.1 g = f g ∧ ∀ q, g • q = mk' U g * q := by tauto
      have k p q r (m : M) : c p (q * r) • m = (c p q - (c q r - c (p * q) r)) • m := ?_
      have S := (mulRight_bijective γ).sum_comp
      ⟨Quot.ind fun x ↦
        ⟨(have ⟨a, _, e⟩ := (ker_mkQ _).le <| shapiroH2_injective U · (a₁ := (M.const _).mapH2 ⟦x⟧)
        (H ⟨D ∘ a, ?_, (eq_of_eq congr(D $(e · ·)) ?_)⟩).rec fun ε t ↦ have P (v : Γ ⧸ U.1 → ℤ) l :=
            (congr($(S (v • a l)) - M.sum _
            (v • $(t l)) + $((mulLeft_bijective ↑l).sum_comp (v • ρ _ l ε))))
          ((ofBase_bijective _).2 ⟨M.sum _ ε, (eq_of_eq congr($(P 1 ·)) ?_)⟩).imp fun _ ↦
            (·.substr <| (Submodule.Quotient.eq _).2 ⟨fun g ↦ a g γ - M.ρ g (M.sum _ (c g • ε)), ?_,
            fun g l ↦ eq_of_eq congr($(e g l) γ + c g l • $(P 1 (g * l)) - M.ρ
            g $(by simpa [*] using P (c g) l)) ?_⟩)), (·.choose_spec ▸ resH2_cyclicClass_eq_zero
        (one_smul ..) ?_)⟩, fun w ↦ ⟨(have ⟨a, _, e⟩ := (ker_mkQ _).le ·
        (H ⟨fun g q ↦ c g (g⁻¹ • q) • w - a g, ?_, (eq_of_eq congr(fun _ ↦ -$(e · ·)) ?_)⟩).rec
          fun η t ↦ (shapiro_H0 U ⟨(w - c · γ • w.1) - D η, (eq_of_eq congr(D $(t ·)) ?_)⟩).imp (by
          simp_all [corestrictH0, D, U])), (cyclicClass_corestrictH0 U χ _ ·.choose_spec 0 (bot_le
        (a := ((cyclicClass _).flip _).ker) (Subtype.ext (_root_.funext (·.2)))).symm ▸ ?_)⟩⟩ <;>
  (try fun_prop) <;> simp +zetaDelta [funext_iff, DiscreteModule.const, j,
  mul_assoc, M.H0.coe_mem _ _] <;> intros <;> match_scalars <;> qify [mul_one] <;> abel_nf

variable [IsScalarTower K L Ω] [IsAlgClosed Ω] [Module.Finite K L] [Algebra.IsSeparable K L]

lemma corestrictH0_ofBase_eq_norm U [J : IsProGalois U.1 L Ω] (y : Lˣ) :
    (unitsModule Γ).corestrictH0 U (ofBase _ Ω (.ofMul y)) =
  ofBase Γ Ω (.ofMul (y.map (Algebra.norm K))) := DiscreteUnits.ext (by
  simp [corestrictH0, norm_eq_prod_embeddings]; apply Finset.prod_bijective (toAlgHom K Ω ·.out
    |>.domRestrict L) (Function.Injective.bijective_of_nat_card_le (fun _ _ H ↦ out_equiv_out.1
    (leftRel_apply.2 (eq_fixingSubgroup_of_isProGalois.1.ge (by simpa [mem_fixingSubgroup_iff,
    mul_smul, inv_smul_eq_iff] using! (congr($H ·).symm)))))
    ((card_algHom_le_finrank ..).trans eq_fixingSubgroup_of_isProGalois.2.ge)) <;> aesop)

lemma cyclicClass_eq_zero_iff_norm {χ : QZChar Γ} [J : IsProGalois (QZChar.ker χ) L Ω] x :
    cyclicClass _ χ (ofBase Γ Ω (.ofMul x)) = 0 ↔ ∃ z : Lˣ, z.map (Algebra.norm K) = x := by
  erw [(QZChar.cyclicClass_spec χ).2, (ofBase_bijective _).2.exists]
  simp [corestrictH0_ofBase_eq_norm, DiscreteUnits.ext_iff, Units.ext_iff]
