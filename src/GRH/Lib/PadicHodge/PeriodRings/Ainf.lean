import GRH.Lib.PadicHodge.PeriodRings.CpIntegers
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: Tilt of O_C, A_inf, theta, epsilon, xi, mu, actions; tilt is algebraically closed. -/

noncomputable section

attribute [-simp] IsUnit.dvd pow_left_inj₀ map_smul


open MulSemiringAction Polynomial PreTilt IsOfFinOrder nonZeroDivisors WittVector Perfection
  NeZero Ideal.Quotient Fact ZMod ValuationRing Cardinal Complex IsPrimitiveRoot

lemma mk_complex_eq_mk_padicAlgCl {p} [Fact p.Prime] : #ℂ = #(PadicAlgCl p) := mk_complex ▸
  (continuum_le_cardinal_of_module ℚ_[p] _).antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p]
  _).trans (by simpa using! mk_quotient_le.trans (@mk_set_le (ℕ → ℚ) _)))

variable {p} [ThePrime p]

/-- The monoid ℕ × G_p, with G_p the absolute Galois group of Q_p; on the period rings with a
Frobenius φ, the pair (n, g) acts as φ^n g. -/
abbrev FrobGal := Multiplicative ℕ × Gp p

/-- The ring O^♭, the inverse limit of O_C/p along x ↦ x^p, where O_C is the ring of integers of
C_p. -/
@[instance_reducible] def OFlat := PreTilt OC p
deriving CommRing, CharP _ p, PerfectRing _ p, IsDomain, ValuationRing

/-- The ring A_inf of p-typical Witt vectors over the tilt O^♭ of the ring of integers of C_p. -/
abbrev Ainf := WittVector p OFlat

/-- The fraction field C^♭ of the tilt O^♭ of the ring of integers of C_p. -/
@[instance_reducible] def CFlat := FractionRing OFlat
deriving Field, Algebra OFlat, IsFractionRing OFlat, FaithfulSMul OFlat, CharP _ p

/-- The ring W(C^♭) of p-typical Witt vectors over the fraction field C^♭ of O^♭. -/
@[instance_reducible] def WittCFlat := WittVector p CFlat deriving CommRing, IsDomain

/-- Fontaine's ring homomorphism θ from A_inf to the ring of integers of C_p, sending the
Teichmüller lift [x] to x^♯. -/
abbrev theta : Ainf →+* OC := fontaineTheta ..

@[simp] lemma theta_teichmuller x : theta (teichmuller p x) = x.untilt :=
  fontaineTheta_teichmuller x

instance {G} [AddCommMonoid G] [Module ℚ≥0 G] : PerfectRing (Multiplicative G) p :=
  ⟨mod_cast @MulAction.bijective₀ ℚ≥0 G _ _ p out⟩

/-- Every homomorphism a from the additive group ℚ to the multiplicative monoid of C_p with a(1)
= 1 lifts to the tilt: some homomorphism χ: ℚ → O^♭ has χ(s)^♯ = a(s) for all s. -/
lemma exists_tilt_lift_of_character (a : Multiplicative ℚ →* ℂ_[p]) (k : a (.ofAdd 1) = 1) : ∃ χ : _
  →* OFlat, ∀ s, (χ s).untilt = a s := ⟨.comp (mapMonoidHom ..) (liftMonoidHom _ _ _ (a.codRestrict
  _ fun s ↦ mem_OC.2 (of_pow (by simp [← map_pow, show s ^ s.toAdd.den = .ofAdd 1 ^ s.1 by aesop,
  k]) s.toAdd.3).norm_eq_one.le)), fun _ ↦ by erw [teichmuller₀_mapMonoidHom_idealQuotientMk]; simp⟩

/-- The map s ↦ ε^s: a chosen homomorphism from ℚ to the multiplicative monoid of O^♭ with
(ε^s)^♯ a primitive root of unity of order the denominator of s. -/
def epsPow :=
  (exists_tilt_lift_of_character ⟨⟨(algebraMap _ _ <| (IsAlgClosed.ringEquiv_of_equiv_of_charZero
  (mk_complex ▸ cantor _) (Quotient.exact (@mk_complex_eq_mk_padicAlgCl p _))).some <|
  exp <| 2 * Real.pi * I * ·.toAdd), by simp⟩, by simp [mul_add, exp_add]⟩ (by simp)).choose

/-- For every rational number s, the untilt (ε^s)^♯ of the element ε^s of O^♭ (`epsPow`)
is a primitive root of unity of order the denominator of s. -/
lemma isPrimitiveRoot_untilt_epsPow s : IsPrimitiveRoot (epsPow s).untilt s.toAdd.den := by
  erw [← coe_submonoidClass_iff, (exists_tilt_lift_of_character ..).choose_spec] <;>
    simp [map_of_injective, RingHom.injective, EquivLike.injective, isPrimitiveRoot_exp_rat]

/-- A chosen element e of O^♭ with (e^p)^♯ = 1 and e^♯ ≠ 1; it is ε^{1/p} for a compatible
system ε = (1, ζ_p, ζ_{p²}, …). -/
def epsRoot := epsPow (.ofAdd p⁻¹)

/-- The element ε = (1, ζ_p, ζ_{p²}, …) of O^♭, defined as the p-th power of the chosen element
ε^{1/p}. -/
def epsTilt := epsRoot ^ p

@[simp] lemma epsPow_one : epsPow (.ofAdd 1) = epsTilt := by simp [epsTilt, epsRoot, ← map_pow,
  ← ofAdd_nsmul]

/-- The element ε = (1, ζ_p, ζ_{p²}, …) of O^♭ has untilt ε^♯ = 1. -/
@[simp] lemma untilt_epsTilt :
  epsTilt.untilt = 1 := by simpa using isPrimitiveRoot_untilt_epsPow (.ofAdd 1)

/-- The element τ = [ε^{1/p}] − 1 of A_inf, where the brackets denote the Teichmüller lift. -/
def tau : Ainf := teichmuller p epsRoot - 1

/-- The element μ = [ε] − 1 of A_inf, where the brackets denote the Teichmüller lift. -/
def mu : Ainf := teichmuller p epsTilt - 1

/-- The element ξ of A_inf equal to the sum of [ε^{1/p}]^i for 0 ≤ i < p, so that ξτ = μ. -/
def xi : Ainf := ∑ i ∈ .range p, teichmuller p epsRoot ^ i

/-- In A_inf one has ξτ = μ, where τ = [ε^{1/p}] − 1 and μ = [ε] − 1. -/
lemma xi_mul_tau : xi * tau = mu := by erw [geom_sum_mul, mu, map_pow]

/-- Every monic polynomial of positive degree over O^♭, the tilt of the ring of integers of C_p,
has a root in O^♭. -/
lemma OFlat.isAIC : IsAIC OFlat := ⟨fun f hf h ↦ by
  have K n w {d} : ∀ b {g}, IsMonicOfDegree g d → ∃ a : OFlat, ((d, a) = (0, b) ∨ g.IsRoot (a.coeff
      n)) ∧ g.eval (w.coeff n) ∣ (w - a).coeff n ^ d := d.rec (by simp) fun _ ih _ g ⟨k, m⟩ ↦ by
    obtain ⟨b : OFlat, q, rfl⟩ := by
      simpa [(coeff_surjective ((IsAIC.of_surjective mk_surjective).exists_pow_eq p) n).exists,
        ↓← dvd_iff_isRoot, k] using (IsAIC.of_surjective mk_surjective).1 g m
    let ⟨a, _, e⟩ := ih b ((isMonicOfDegree_X_sub_one _).of_mul_left ⟨by omega, m⟩)
    obtain t|t := dvd_total (w - a) _ <;> [use b; use a] <;> simp [← map_sub, ← coeff_def] <;>
      grw [e, t, pow_succ']; aesop
  choose a ha e using (K · · 0 ⟨rfl, hf.map (coeff ‹_›)⟩)
  simp_all [h.ne']
  use ⟨fun n ↦ ((n + f.natDegree).succ.rec 0 a : OFlat).coeff n, ?_⟩, ext ?_ <;> intro
  erw [coeff_pow_p', add_right_comm, eq_comm, ← sub_eq_zero, ← map_sub, ← coeffMonoidHom_pow_p_pow']
  grw [← zero_dvd_iff, ← ha, ← PreTilt.coeff_pow_p, e, pow_succ, pow_mul, ← Nat.lt_pow_self out];
    rfl
  erw [← eval₂_hom, eval₂_hom _ (a ..), ← coeffMonoidHom_pow_p_pow', ha, zero_pow out]; rfl⟩

variable {A R N S} [CommRing A] [MulSemiringAction FrobGal A] [SMul N A] [CommRing R] [CharP R p]
  [CommRing S] {M} [Monoid M] (n : ℕ) (g : Gp p) (x : OFlat)

/-- For a ring A with an action of ℕ × G_p, the ring endomorphism given by the generator of ℕ
paired with the identity of G_p, the Frobenius φ. -/
def frobEnd := toRingHom FrobGal A (.ofAdd 1, 1)

/-- `W(R)` is a `ℤ_p = W(𝔽_p)`-algebra for every ring `R` of characteristic `p`. -/
instance : Algebra ℤ_[p] (WittVector p R) :=
  ((WittVector.map (castHom dvd_rfl R)).comp (equiv p).symm).toAlgebra

/-- `W(S)` is a `W(A)`-algebra for every `A`-algebra `S`. -/
instance (priority := low) [Algebra A S] : Algebra (WittVector p A) (WittVector p S) :=
  (WittVector.map (algebraMap ..)).toAlgebra

/-- Frobenius and `G_p` act on `O^♭`. -/
instance actOFlat :
  MulSemiringAction FrobGal OFlat := by apply (actionOfHoms _ fun m ↦ (iterateFrobenius _ p
  m.1.toAdd).comp (tiltMap (toRingHom _ _ m.2))) <;> simp [iterateFrobenius_def, ← tiltMap_comp,
  pow_add, pow_mul', RingHom.ext_iff] <;> [convert tiltMap_id; congr!] <;> aesop (add simp mul_smul)

instance (priority := 100) FrobGal.galAct : MulSemiringAction (Gp p) A :=
  compHom (M := FrobGal) _ (.inr ..)

@[instance 100] lemma FrobGal.smulCommClass_gal [SMulCommClass FrobGal N A] :
  SMulCommClass (Gp p) N A := SMul.comp.smulCommClass _

@[local simp] lemma FrobGal.smul_def (x : A) : (Multiplicative.ofAdd n, g) • x =
  frobEnd^[n] (g • x) := by erw [smul_iterate_apply, smul_smul]; congr <;> simp

@[simp] lemma smul_frobEnd (x : A) : g • frobEnd x = frobEnd (g • x) := by erw [smul_smul]; simp

/-- For n and x in O^♭, the element (x^{1/p^n})^♯ of the ring of integers of C_p, the untilt of
the p^n-th root of x. -/
def OFlat.untiltRoot := untilt ((frobeniusEquiv _ p).symm^[n] x)

lemma OFlat.mk_untiltRoot : ↑(untiltRoot n x) = x.coeff n := by simp [untiltRoot]

open algebraMap

lemma wittVector_map_algebraMap [CharP S p] (f : R →+* S) (a : ℤ_[p]) : map (p := p) f a =
  algebraMap _ _ a := congr(map $((f.comp _).ext_zmod _) _)

instance [MulSemiringAction M R] : SMulCommClass M ℤ_[p] (WittVector p R) :=
  ⟨fun _ ↦ map_smul (AlgHom.mk _ (wittVector_map_algebraMap _))⟩

instance [MulSemiringAction M Ainf] [MulSemiringAction M S] [Algebra ℤ_[p] S] [Algebra Ainf S]
    [IsScalarTower ℤ_[p] Ainf S] [SMulCommClass M ℤ_[p] Ainf] [SMulDistribClass M Ainf S] :
    SMulCommClass M ℤ_[p] S := ⟨by simp [← algebraMap_smul Ainf, smul_distrib_smul]⟩

instance [CharP S p] [Algebra R S] : IsScalarTower ℤ_[p] (WittVector p R) (WittVector p S) :=
  .of_algHom ⟨_, wittVector_map_algebraMap _⟩

lemma OFlat.frobEnd_apply : frobEnd x = x ^ p := (pow_mul ..).trans congr($(one_smul FrobGal x) ^ p)

variable {G} [Group G] [MulSemiringAction G OFlat] [MulSemiringAction FrobGal S]

instance [SMul S A] [SMulDistribClass FrobGal S A] : SMulDistribClass (Gp p) S A :=
  ⟨(smul_distrib_smul <| (1, ·) ·)⟩

@[simp] lemma frobEnd_algebraMap [Algebra S A] [SMulDistribClass FrobGal S A] (x : S) :
    frobEnd (x : A) = frobEnd x := smul_algebraMap_eq_algebraMap_smul ..

instance : MulSemiringAction G CFlat := IsFractionRing.mulSemiringAction _ OFlat _

deriving instance Algebra ℤ_[p], Algebra Ainf, IsScalarTower ℤ_[p] Ainf,
  MulSemiringAction G, SMulCommClass G ℤ_[p] for @WittCFlat p _

instance : SMulDistribClass G Ainf WittCFlat := smulDistribClass_of_tower fun _ : Ainf ↦ ext fun _ ↦
  smul_algebraMap_eq_algebraMap_smul ..

instance : CharP (IsLocalRing.ResidueField OFlat) p := .of_ringHom_of_ne_zero (mk _) _ out

instance : IsAlgClosed CFlat := (OFlat.isAIC.of_isLocalization _⁰).isAlgClosed
