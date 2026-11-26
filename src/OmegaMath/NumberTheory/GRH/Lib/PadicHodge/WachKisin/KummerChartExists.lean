import OmegaMath.NumberTheory.GRH.Lib.PadicHodge.WachKisin.PeriodMatrixBasis
import OmegaMath.NumberTheory.GRH.Lib.GaloisRep.Main.LocalEmbedding
import OmegaMath.NumberTheory.GRH.Lib.General.NumberTheory.Valuation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: Weil pairs (s, m): products, powers, uniqueness of m. Embedding of W(F_q)
into algebraic closure of Q_p via θ; fixers agree. Action of Frobenius and Galois group on A_inf,
W(C^♭); Teichmüller roots of unity. Every p-adic field has a Kummer chart from a uniformiser and its
root tower. -/

noncomputable section

section

variable {p} [ι : ThePrime p] {m m' Γ s t} [Group Γ] {j : Γ →* _} (h : IsWeilPair (j s) m)
include h

/-- Weil pairs multiply: if (s, m) and (t, m') are Weil pairs, then so is (st, m + m'). -/
lemma IsWeilPair.mul : IsWeilPair (j t) m' → IsWeilPair (j (s * t)) (m + m') :=
  (by simpa [IsWeilPair, p.pow_add', ·.mul_iff])

lemma IsWeilPair.pow n :
  IsWeilPair (j (s ^ n)) (n * m) := by simpa [← pow_mul'] using! IsFrob.pow h n

/-- If (s, m) is a Weil pair and s⁻¹ acts as x ↦ x^q modulo the maximal ideal of the valuation
ring of Q̄_p, then q = p^m; in particular m = 0 if q = 1. -/
lemma IsWeilPair.eq_pow_of_isFrob {q} (b : IsFrob (intQpBar p) q (j s)⁻¹) : q = p ^ m := by
  let ⟨l, _, P⟩ := p.succ.exists_infinite_primes; have := Fact.mk P
  refine mod_cast (b.cycChar_eq l ?v).symm.trans (h.cycChar_eq l ?v)
  grind [Nat.prime_def, ι.out, valuation_natCast_eq_one]

omit h

namespace Lift

open WittVector
variable {p : _} [ThePrime p] {𝔣} {g : Gp p} {c : WittFq 𝔣}

/-- The Z_p-algebra homomorphism from Λ = W(F_{p^f}) to Q̄_p that becomes the restriction of θ
after the inclusion of Q̄_p in C_p. -/
def wittToQpBar :=
  (exists_algHom_lift (OC.toPadicIntAlgHom (theta.comp (algebraMap (WittFq 𝔣) _)))).choose

lemma coe_wittToQpBar : wittToQpBar c = (theta (algebraMap _ _ c)).1 :=
  ((exists_algHom_lift _).choose_spec c).symm

lemma wittToQpBar_injective : Function.Injective (@wittToQpBar p _ 𝔣) := .of_ker _
  (Ideal.eq_bot_of_liesOver_bot ℤ_[p] (.comap _ ⊥)).le

lemma smul_witt_eq_iff : g • algebraMap _ Ainf c = algebraMap _ _ c ↔ g (wittToQpBar c) =
  wittToQpBar c := (c.exists_smul_algebraMap_eq _).rec fun _ e ↦ by erw [e,
  (map_injective _ Subtype.val_injective).eq_iff, ← wittToQpBar_injective.eq_iff,
  ← UniformSpace.Completion.coe_inj, coe_wittToQpBar, ← e, theta_smul]; simp [← coe_wittToQpBar]

end Lift

end

namespace Lift

open WittVector MulSemiringAction HasEnoughRootsOfUnity OFlat
variable {p} [ThePrime p] [Γ : GroupOverGp p] {f : ℕ+}

/-- The group ℤ × Γ (ℤ written multiplicatively); on rings with bijective Frobenius φ, such as
A_inf, the pair (n, g) acts as φ^n j(g). -/
def FrobGroup (Γ : GroupOverGp p) := Multiplicative ℤ × Γ deriving Group

/-- The projection homomorphism from ℤ × Γ (`Lift.FrobGroup`) onto its second factor Γ. -/
def FrobGroup.snd : FrobGroup Γ →* Γ := .snd ..

/-- The element (1, identity) of the group ℤ × Γ (`Lift.FrobGroup`), the one that acts as the
Frobenius φ. -/
def FrobGroup.φ : FrobGroup Γ := (.ofAdd 1, 1)

/-- The inclusion homomorphism Γ → ℤ × Γ sending g to (0, g). -/
def FrobGroup.inr : Γ →* FrobGroup Γ := .inr ..

instance : MulSemiringAction (FrobGroup Γ) OFlat :=
  .compHom _ ((zpowersHom _ (frobeniusEquiv OFlat p)
  ).noncommCoprod ((toRingAut ..).comp toGp) fun _ _ ↦ .zpow_left (by ext1; simp [frobenius_def]) _)

lemma phi_smul_oFlat (x : OFlat) : FrobGroup.φ • x = frobEnd x :=
  x.frobEnd_apply ▸ congr($(one_smul (FrobGroup Γ) x) ^ p)

lemma frobGroup_phi_smul (x : Ainf) : FrobGroup.φ • x = frobEnd x := ext fun _ ↦ phi_smul_oFlat _

lemma phi_smul_wittCFlat (x : WittCFlat) : FrobGroup.φ • x = frobenius x :=
  frobenius_eq_map_frobenius p (R := CFlat) ▸ congr(x.map $(IsFractionRing.ringHom_ext (A :=
  OFlat) (by simp [frobenius_def, phi_smul_oFlat, frobEnd_apply])))

lemma FrobGroup.phi_pow_smul n (x : Ainf) : φ ^ n • x =
  frobEnd^[n] x := by simp [← funext frobGroup_phi_smul]

omit Γ

lemma isUnit_teichmuller_sub {a b : flatFq f} (h : a ≠ b) : IsUnit
  (teichmuller p a - teichmuller p b) := by simpa [Ainf.isUnit_iff_isUnit_constantCoeff, map_sub]

instance : HasEnoughRootsOfUnity (flatFq f) (p ^ f.val - 1) :=
  of_card_le (by simp [← card_flatFq, ← Nat.card_units])

/-- Let k be the field of p^f elements in O^♭ and s: W(k) → K a ring homomorphism to a field.
Every x in K with x^{p^f} = x is s([a]) for the Teichmüller lift [a] of some a in k. -/
lemma exists_flatFq_root {K} [Field K] (s : WittFq f →+* K) x (H : x ≠ 0 → x ^ (p ^ f.val - 1) =
  1) : ∃ a, s (teichmuller p a) = x := prim.rec fun g h ↦ by_cases (⟨0, by simp [·]⟩) (H · |>
  (h.map_of_injective (f := s.1.comp _) fun _ _ ↦
  (by simpa using isUnit_teichmuller_sub · |>.map s).mtr
  ).eq_pow_of_pow_eq_one |>.imp' (g ^ ·) (by simp))

lemma fixes_roots_iff_fixesLambda g : (∀ ζ, ζ ^ (p ^ f.val - 1) = 1 → g ζ = ζ) ↔ FixesLambda f g :=
  ⟨fun h c ↦ ext (c.1 · |> fun a ↦ congr($(smul_witt_eq_iff (c :=
  teichmuller p a).2 (by grind [(a ^ p ^ _).ext a.2, NeZero.one_le, pow_sub₀])).1 0)), fun h _ e ↦
  (exists_flatFq_root _ _ fun _ ↦ e).choose_spec ▸ smul_witt_eq_iff.1 (h _)⟩

end Lift

open Fint Ideal IsLocalRing NeZero OFlat PadicComplex PowerSeries PreTilt WittVector

attribute [-simp] pow_left_inj₀

variable {p : outParam ℕ} [ThePrime p] (C : Subgroup (Gp p)) (Γ : outParam (GroupOverGp p))

/-- Let C be a closed subgroup of G_p that is transitive on the n-th roots of π for every n > 0.
If u, v in O^♭ have untilts with e-th power π, e > 0, then some g in C sends the Teichmüller
lift [u] to [v]. -/
lemma Lift.exists_smul_teichmuller_eq [hC : @IsClosed (Gp p) _ C] {π : PadicAlgCl p} (H :
  ∀ {x y n}, 0 < n → x ^ n = π →
  y ^ n = x ^ n → ∃ g ∈ C, g • x = y) (u v : OFlat) e [NeZero e] (hu : (u.untilt ^ e).1 = π)
  (hv : v.untilt ^ e = u.untilt ^ e) : ∃ g ∈ C, g • teichmuller p u = teichmuller p v := by
  choose! b A B using fun y (_ : untilt y ^ e = u.untilt ^ e) n ↦ by simpa [← coe_eq] using
    (IsAIC.exists_root_map_eq (f := algebraMap ..) (Polynomial.monic_X_pow_sub_C π (ne (p ^ n * e)))
   (x := (untiltRoot n y).1) (by simp [pow_mul, ← SubmonoidClass.coe_pow, untiltRoot, coe_eq, *]))
  have cl n := hC.inter (isClosed_setOf_smul (b u n) (· = (v.untiltRoot n).1))
  refine ((cl 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ (fun n _ ↦
    .imp_right fun h ↦ by simpa [← smul_coe_Cp, B, untiltRoot, ↓Function.iterate_succ',
    ← untilt_iterate_frobeniusEquiv_symm_pow (_^[n] _) 1] using congr($h ^ p))
    (fun n ↦ by simpa [← B v hv] using! H (pos _) (A u rfl n) (by simp [*])) cl).imp
   fun g h ↦ ⟨(h _ ⟨0, rfl⟩).1, (map_teichmuller ..).trans (congrArg _ (Perfection.ext fun n ↦ ?_))⟩
  erw [map_pow, pow_one, ← coeff_tiltMap _ (mk_untiltRoot ..), ← mk_untiltRoot]
  congr 1 with; simpa [← B] using (h _ ⟨n, rfl⟩).2

/-- A Kummer chart: a chart and a subgroup Γ' of index prime to p, containing the elements near
1, with j(Γ') the fixer of Λ and θ(z), containing for each l ≥ 0 a g with gz = [ε]^l z. -/
class Lift.KummerChart extends chart : Chart where
  (Γ' : Subgroup Γ) (index_coprime : Γ'.index.Coprime p) fixes (g : Γ') :
    chart.FixesThetaZ (toGp g.1)
  isChartOf : chart.IsChartOf (toGp.comp Γ'.subtype)
  nearOne_le : nearOne Γ ≤ .map Γ'.subtype ⊤
  exists_smul_z l : ∃ g : Γ', toGp g.1 • chart.z.1 = teichmuller p epsTilt ^ l * chart.z

@[simp] lemma Lift.KummerChart.thetaPhiInv_phi_pow [GroupOverGp p] a r : thetaPhiInv a (FrobGroup.φ
  ^ a • r) = theta r := a.rec (by aesop) (by simp [pow_succ', mul_smul, frobGroup_phi_smul])

variable {Γ} [k : Lift.KummerChart Γ]

/-- The number d = 0 if the index e of the chart is 1, and d = v_p(e) + 1 otherwise. -/
def Lift.KummerChart.differentExp := if k.e = 1 then 0 else padicValNat p k.e + 1

/-- The Kummer chart is unramified: E = z + p, the index e is 1, and d = 0. -/
def Lift.KummerChart.IsUnramified := k.E = k.z + p ∧ k.e = 1 ∧ differentExp = 0

lemma Lift.KummerChart.chart_isChartOf : k.chart.IsChartOf Γ.overGp.toGp :=
  (k.isChartOf · · |>.elim (⟨·, ·⟩))

/-- If j(Γ) is open, there is a chart over Λ = W(F_{p^f}) with ef = [G_p : j(Γ)] such that j(Γ)
fixes Λ and θ(z), contains the fixer of θ(S), a p^f-Frobenius and elements with gz = [ε]^l z
for all l ≥ 0; e = 1, E = z + p if j(Γ) contains inertia. -/
lemma Lift.exists_kummer_chart Γ [Group Γ] [𝒥 : OverGp Γ p] : ∃ k : KummerChart ⟨Γ⟩,
  (∀ g, k.FixesThetaZ (𝒥.toGp g)) ∧ k.e * k.f = 𝒥.toGp.range.index ∧ (inertiaGroup _ (intQpBar p) ≤
  𝒥.toGp.range → k.IsUnramified) ∧ ∃ φ ∈ 𝒥.toGp.range, IsFrob (intQpBar p) (p ^ k.f.val) φ := by
  obtain ⟨L, ⟨⟨e, f, ⟨⟨_, ⟨h2⟩⟩⟩⟩⟩⟩ := @residueCard_padic p _ ▸ IsLocalGalois.of_finite ⟨_, 𝒥.2.1⟩
  lift f to ℕ+ using Ne.pos (by simpa [·, *] using L.6.one_lt_card)
  obtain ⟨⟨⟨φ, hφ⟩, ⟨D⟩⟩, ⟨⟩, π, hπ⟩ := h2 ▸ L.frobenius_spec, id L, L.5.exists_irreducible
  let ⟨v, hv⟩ : Associated (π ^ e) (-p) := by simpa [← dvd_dvd_iff_associated, ← ge_antisymm_iff,
    dvd_iff_valuationVia_le, valuationVia] using! ((isUniformiser_ell.val_pow_eq_iff_mul_ordRat
    isLocalGalois_padic _ 1).2 (by simpa [*] using
    (isUniformiser_iff_irreducible.2 ⟨_, hπ⟩).ordRat_eq_one L (π := .mk0 π (mod_cast hπ.ne_zero))))
  wlog v₁ : e = 1 → v = 1 generalizing π v
  apply this _ ((irreducible_mul_units v).2 hπ) 1 <;> simp [of_not_imp v₁, ← hv]
  have hf (g : 𝒥.toGp.range) := (@fixes_roots_iff_fixesLambda p _ f g).1 fun ζ e ↦
    (D hφ).induction_on g
    (isClosed_setOf_smul _ (· = _)) fun n ↦ (apply_eq_pow_of_isFrob ((hφ.pow _).mul_iff.2 n.2.2)
    not_dvd_pow_sub_one e).trans (by simp [pow_eq_pow_of_modEq ((Nat.modEq_sub one_le).pow _) e])
  let κ := ((algebraMap ..).comp (localFieldOf Γ).val.1).restrict
    (valRingBelow _ (intQpBar p)) 𝓞_ℂ_[p] (by simp [← coe_nnnorm])
  obtain ⟨ev, _, H⟩ := exists_chart_of_pow_mul_eq_neg f (v.map κ) (by simpa using congr(κ $hv))
  have : IsHausdorff (span {κ π}) OC := ⟨fun x h ↦
    eq_of_forall_pow_dvd_sub p fun _ ↦ by grw [← map_natCast κ,
    neg_dvd.1 (Associated.dvd' ⟨v, hv⟩), map_pow, ← pow_mul, smodEq_span_pow_iff_dvd.1 (h _)]⟩
  choose V hV using dsimp% mem_range_of_approx (π := @X (WittFq f) _) (π' := κ π) (theta.comp
    ev.1).toAddMonoidHom (by simp [*]) κ fun x ↦ let ⟨a, h⟩ := (exists_flatFq_root ((residue _).comp
    ((wittToQpBar.1.codRestrict (localFieldOf _) fun _ _ ↦ smul_witt_eq_iff.1 (hf ..)).codRestrict _
      fun _ ↦ by simpa using! coe_wittToQpBar ▸ (_ : OC).2)) (residue _ x) (by simp [·, ← h2,
      FiniteField.pow_card_sub_one_eq_one]))
    ⟨C (teichmuller p a), ((hπ.maximalIdeal_eq ▸ mk_span_eq_iff_dvd_sub.1 :) h.symm).imp
    fun y e ↦ by simpa [eq_add_of_sub_eq' e, C_eq_algebraMap] using Subtype.ext coe_wittToQpBar⟩
  obtain ⟨c, rfl, rfl, _, _, a⟩ := H (IsUnit.mul_iff.1 (isUnit_of_mem_nonunits_one_sub_self ((V v -
    V 1 + 1) * V v.2) (by simpa [*, ← map_mul κ] using ·.map ev |>.map theta))).1.unit (by simp [*])
  refine ⟨⟨c, ⊤, ?_, ?_, fun σ H ↦ cast ?_ ((fixingSubgroup_fixedFieldOf _).le fun x ↦ by
    obtain h | h := (valRingBelow (localFieldOf Γ) (intQpBar p)).2 x <;> simpa [*, κ, ← coe_eq,
      Subtype.ext_iff] using c.smul_theta_of_fixesThetaZ H ⟨_, V ⟨_, h⟩, rfl⟩), ?_, fun l ↦
    cast ?_ (exists_smul_teichmuller_eq 𝒥.toGp.range (L.exists_inertia_smul_eq_of_pow_eq (π :=
    .mk0 π.1 (mod_cast hπ.ne_zero)) (isUniformiser_iff_irreducible.2 ⟨_, hπ⟩) · · · |>.imp' (↑) ?_)
    c.varpiFlat (epsTilt ^ l * c.varpiFlat) 1 ?_ ?_)⟩, ?_, ?_, ?_, φ, φ.2, hφ⟩ <;> simp +contextual
    [*, a.eq, c.z_eq_teichmuller, κ, Chart.E, ← coe_eq, mem_localFieldOf.1, Subtype.ext_iff,
    KummerChart.IsUnramified, KummerChart.differentExp, Chart.FixesThetaZ, FixesLambda, hf ⟨_, _⟩]
