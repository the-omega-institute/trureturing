/- GID: D5/S3/Zeros/GRH/New/Selmer/Corepresentable
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/Corepresentable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.Corepresentable. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/Corepresentable.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology.TameCocycles
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols,
Herbrand quotient. Source: J.-P. Serre, Galois Cohomology (1997); Neukirch–Schmidt–Wingberg,
Cohomology of Number Fields (2nd ed. 2008), Ch. I, VI; Atiyah–Wall, Cohomology of groups, in
Cassels–Fröhlich (1967), IV §8. Form here: Explicit continuous cocycles only; Shapiro's lemma only
as injectivity; corestriction is summation on functions on a coset space; Tate's lemma on the
Herbrand quotient is an index formula for a group of prime order.

Set-up for this proof: Ribet's method with congruent blocks and tied auxiliary primes. Ribet's
method in any rank, with congruent blocks and tied primes, gives a Hecke element, polynomial in the
tie parameters, that kills a determinant vanishing on lifts modulo the ties. On lifts it has no term
below the product of all parameters, whose coefficient has valuation bounded without the even
classes. Literature: Fitting-ideal forms of Ribet's method are known for distinct blocks in any rank
and congruent characters in rank 2. Related work: Dasgupta–Kakde–Silliman–Wang, The residually
indistinguishable case of Ribet's method for GL2, 2023; Bellaïche–Chenevier, Families of Galois
representations and Selmer groups, 2009; Urban, Selmer groups and the Eisenstein–Klingen ideal,
2001.

Part of: One anticyclotomic twist makes all Selmer groups short (see New.Selmer.TwistForRows).

Part of: Tied conditions at new primes shrink Selmer groups (see New.Selmer.TwistTheorem).

This file: New primes with anticyclotomic characters, auxiliary sets, families of interpolated
L-values. Anticyclotomic character of order ℓ^N ramified at one new prime with prescribed Frobenius.
Even classes, new places with tame generators, triangular system of primes. Balanced
representations, pencils of tied primes, ties, twists at a point. Selmer groups are finitely
presented: cocycles unramified off S read at finitely many points. -/

open Fintype IsDiscreteValuationRing Module Multiplicative NonarchimedeanGroup QZ QuotientGroup Set
  Subgroup Submodule Matrix.Module

variable (E) [Field E] [UnramCMField E] {E'} [Field E'] [UnramCMField E'] (S I' :
  Finset (FinPlace E')) {q ℓ : ℕ}

/-- The data at an auxiliary prime: a place A of Ω, elements γ and φ of Gal(Ω/E), and a
homomorphism h from Gal(Ω/E) to ℤ/q. -/
structure AuxPrimeData (q) where
  place : ClosurePlace
  (γ φ : Gal(Ω/E)) h : Gal(Ω/E) →* Multiplicative (ZMod q)

variable {E : Type} [Field E] [UnramCMField E]

/-- NP ≡ 1 mod q, A lies over P, φ is an arithmetic Frobenius and γ the chosen tame generator at
A, and h satisfies `IsFromU1` for T, {P}, sending γ to 1 ∈ ℤ/q. -/
structure IsAnticyclotomicAt (T P) {q : ℕ} (l : AuxPrimeData E q) extends IsFromU1 T {P} l.h where
  norm_modEq : P.q ≡ 1 [MOD q]
  isPlaceOver : IsPlaceOver l.place P
  isFrob : IsFrob l.place P.q l.φ
  notMem : P ∉ T
  tame_gen : l.γ ∈ inertiaGroup _ l.place ∧ l.h l.γ = .ofAdd 1 ∧ isPlaceOver.tameGenerator = l.γ

/-- I is auxiliary for the finite set S: every place v of I has prime norm, v and v̄ lie outside
S, and v̄ lies outside I. -/
@[grind] def IsAuxiliary := ∀ v ∈ I', v ∉ S ∧ v.q.Prime ∧ star v ∉ I' ∧ star v ∉ S

/-- A family: continuous characters ν_i and values val(I, χ), a fixed integral combination of
values of χ for auxiliary I, with val(∅, 1) ≠ 0; for χ anticyclotomic of modulus I, adding P
raises the valuation by ≤ 8c if all v(1 − ν_iχ^{±1}(Frob_P)) ≤ c. -/
structure IsFamily (S : Finset (FinPlace E)) {ℓ : ℕ} {T} [ThePrime ℓ] (ν :
  T → Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) (val : _ → (Gal(Ω/E) →* PadicAlgCl ℓ) → _) where
  continuous_unitary i : Continuous (ν i)
  exists_interp I : IsAuxiliary S I → ∃ (α : Type) (_ : Fintype α) (g c : α → _),
    (∀ a, ‖c a‖ ≤ 1) ∧ ∀ χ, val I χ = ∑ a, c a * χ (g a)
  val_insert_le I : ∀ P ∉ I, IsAuxiliary S (insert P I) → ∀ χ, IsFromU1 (placesDividing E ℓ) I χ →
    ∀ (A : ClosurePlace) φ, IsPlaceOver A P → IsFrob A P.q φ → ∀ c : NNReal, (∀ i (t : ℤˣ),
    ellVal (1 - (ν i φ).1 * χ φ ^ t.1) ≤ c) → ellVal (val (insert P I) χ) ≤ ellVal (val I χ) + 8 * c
  val_empty_ne_zero : val ∅ 1 ≠ 0

variable {E₁ : Type} [Field E₁] [UnramCMField E₁] {ℓ' : ℕ} [ThePrime ℓ] {E Λ J : Type} [Field E]
  [UnramCMField E] [CommRing Λ] {e'} (ν) (w' : J → FinPlace E) (τ φ :
  J → Gal(Ω/E)) (a' : Gal(Ω/E)) (S Q : Finset (FinPlace E))

/-- Let z lie in the normal closure of inertia at a finite set R, off S, S̄ and ℓ. Near z is a
Frobenius σ at a prime P ∉ R ∪ R̄ of prime norm ≡ 1 mod ℓ^N, with an anticyclotomic h to
ℤ/ℓ^N of modulus P, trivial at σ, S and ℓ, sending an inertial γ to 1. -/
lemma exists_isAnticyclotomicAt [ThePrime ℓ'] N (S : Finset (FinPlace E₁)) {R} (h₀ : R.Finite) {z W}
  (h : z ∈ normalClosure (inertiaAbove (R \ (.conjClosure S ∪ placesDividing E₁ ℓ')))) (hW :
  W ∈ nhds z) : ∃ P ∉ R.conjClosure, P.q.Prime ∧ ∃ l : AuxPrimeData E₁ (ℓ' ^ N), l.φ ∈ W ∧
  l.h l.φ = 1 ∧ ∀ T ⊆ ↑S ∪ placesDividing E₁ ℓ', IsAnticyclotomicAt T P l := by
  choose T hS _ B _ using
    exists_sup_idelesUnitOff_eq_top (star '' S ∪ S ∪ placesDividing E₁ ℓ').toFinite _ h₀
  choose s hs using (SUnit.dirichlet_unit_theorem hS).1.1
  choose y hy using (IsAIC.exists_pow_eq (ℓ' ^ N) <| algebraMap E₁ Ω ·)
  choose P hP hp A hA σ H F G using chebotarev ((isOpen_ker_cycCharMod.1.inter (by simp
    [isOpen_iInter_of_finite, stabilizer_isOpen_of_isIntegral])).inter
    isOpen_setOfPred_eventually_nhds) ⟨z, ((cycCharMod Ω (ℓ' ^ N)).ker ⊓ ⨅ u : s,
    MulAction.stabilizer _ (y u.1.1)).normalCore.normalClosure_le_normal (by
    rintro g ⟨v, r, A, a, hg⟩ b; refine
    ⟨cycCharMod_of_mem_inertiaGroup (hg.conj b) ?z, Subgroup.mem_iInf.2 fun u ↦
    inertia_fixes_root_of_unit (hg.conj b)
    ?z (hy _) ((a.smul b).valuationVia_eq_one_iff.2 (u.1.2 _ ?_)) ?_⟩ <;> simp_all [(a.smul
    b).valuation_natCast_eq_one_iff, placesDividing, (B v _).mt]) h 1, hW⟩ (hS.union h₀.cj)
  choose k hk using (Nat.modEq_iff_exists_eq_add hp.pos).1 ((F.mem_ker_cycCharMod_iff
    (by simp [hA.valuation_natCast_eq_one_iff]; grind -abstractProof [placesDividing])).1 H.1.1).symm
  choose _ _ e o _ using hA.exists_localArtin_eq_tameGenerator
  let r := (LocInt P).unitGroupToResidueFieldUnits.comp (.mk' (fun t ↦
    ⟨t * uniformizer P ^ (Valued.v t.1).log,
    (Valued.v.mem_unitGroup_iff ..).2 (by simp [WithZero.exp_neg, -WithZero.inv_exp])⟩)
      (by simp [Subtype.ext_iff, zpow_add]; grind -abstractProof))
  have R t (h : Valued.v (t.1 - 1) < 1) : r t = 1 := Units.ext
    (residue_eq_iff_valuation_sub_lt_one.2 (by simpa [by simpa using Valued.v.map_one_add_of_lt h]))
  have n := (orderOf_eq_card_of_forall_mem_zpowers o).trans (card_ResField P ▸ Nat.card_units _)
  let f := (monoidHomOfForallMemZpowers o (g' := ofAdd (1 : ZMod (ℓ' ^ N))) (by simp [*])).comp r
  have L t : r (t ^ k) = 1 → f t = 1 := (o (r t)).elim fun _ e ↦ by
    simpa [f, ← e, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, n, hk] using
      Int.dvd_of_mul_dvd_mul_right (by grind -abstractProof [hp.one_lt])
  choose η hθ using (((mk' (principalIdele (K := E₁)).range).domRestrict
    (idelesUnitOff T)).liftOfSurjective (MonoidHom.range_eq_top.1
    (comap_injective (mk'_surjective _) (by simpa)))).symm.surjective ⟨(f.comp _).domRestrict _, by
    simp; rintro ⟨_, b⟩ ⟨_, ⟨⟩⟩
    exact mem_span.1 (hs.ge (x := ⟨_, principalIdele_mem_idelesUnitOff.1 b⟩) ⟨⟩)
      ((f.comp (ideleAt P)).comp
    (principalIdele.domRestrict _)).ker.toAddSubgroup.toIntSubmodule fun u hu ↦ L _ (R _ (by
    have v := by simpa [NeZero.ne, ← hy, valuationVia] using
      hA.valuationVia_eq_one_iff.2 (u.2 P (by grind -abstractProof))
    simpa using! (v_algebraMap_eq_valuation (u.1.1 ^ k - 1)).trans_lt
      (hA.isEquiv.lt_one_iff_lt_one.1 (by simpa [← (Subgroup.mem_iInf.1 H.1.2 ⟨_, hu⟩).symm,
      pow_add, pow_mul, *, ← mul_one_sub, Valuation.map_sub_swap] using F.2 _ v.le))))⟩
  let θ := η.comp (mk' _)
  have V a h : θ a = f (ideleAt P a) := congr($hθ.1 ⟨a, h⟩)
  choose h hh d using exists_comp_artinMap Gal(Ω/E₁) (θ.comp (.id _ / starMulAut.toMonoidHom))
    ((continuous_of_continuousAt_one _ ((((Continuous.of_isOpen_ker f (isOpen_of_forall_pow_mem
    (by simp) (pow_index_mem _))).comp_continuousOn (by fun_prop)).congr
    V).continuousAt ((isOpen_idelesUnitOff T).mem_nhds (by simp)))).comp (continuous_id.div'
    continuous_star)) fun x ↦ le_comap_mk' _ η.ker ⟨x / star x, by aesop⟩
  have g := d _ _ (hA.artinAt_eq_of_localArtin_eq e ▸ artinMap_locIdele ..)
  simp [star_locIdele, ↓locIdele_mem_idelesUnitOff, *, f, r, (isSplit_of_q_prime hp).symm] at g
  have F := by simpa using F.mul_iff.2 (hA.tameGenerator ^ (h σ⁻¹).toAdd.val).2
  exact ⟨P, hP ∘ .inr, hp, ⟨A, _, _, h⟩, (G _ F).2.self_of_nhds, by ext; simp [g], fun _ t
    ↦ ⟨⟨(hh.1 · ⟨⟩), θ, (le_comap_mk' _ η.ker ⟨·, rfl⟩), by grind -abstractProof [mem_idelesUnitOff, star_star,
    MonoidHom.comp_apply], d⟩, by simp [*], hA, F, by grind -abstractProof, hA.tameGenerator.2, g, rfl⟩⟩

/-- The even classes: locally constant cocycles c in (O/ℓ^ν)(−e), unramified off ℓ, S and S̄,
with c(g^c) = c(g), vanishing on the elements of decomposition groups above ℓ in ker cyc. -/
def evenClasses (O : CoeffRing ℓ) S ν e := {c ∈ selmerModule (tateTwist ℓ E O e)
  (placesDividing E ℓ ∪ .conjClosure S) ∅ (QuotSpan (ℓ ^ ν : ↑O)) |
  (∀ g, c (conjGal g) = c g) ∧ ∀ g ∈ shaLocalSet ℓ E 1, c g = 0}

/-- Each w_j is a place not above ℓ, φ_j fixes the ℓ^ν-th roots of unity, and τ_j is the chosen
tame generator at some place over w_j. -/
def IsNewPlaces (w : J → FinPlace E) (τ φ : J → Gal(Ω/E)) := ∀ j, w j ∉ placesDividing E ℓ ∧
  cycCharMod Ω (ℓ ^ ν) (φ j) = 1 ∧ ∃ A, ∃ h : IsPlaceOver A (w j), h.tameGenerator = τ j

/-- The family indexed by two copies of J with values τ_j on the first copy and (τ_j^c)⁻¹ on the
second. -/
noncomputable abbrev withConjInv (k : J × _) := idOrConjInv k.2 (τ k.1)

/-- Ordered places w_j, serving twists 0 < ty_j < t, cut down the even classes modulo ℓ^ν one
after another up to ℓ^h; a separates the characters cyc^{−e} up to ℓ^h; c bounds the total
cost. -/
structure IsPrimeTriangle (w : J → FinPlace E) (τ φ : J → Gal(Ω/E)) (a : Gal(Ω/E)) [LinearOrder J]
  [Fintype J] (t) (ty : J →o {e : Fin t // 0 < e.1}) (h c) where
  isNewPlaces : IsNewPlaces ν w τ φ
  detect : ∃ s : Finset _, (card J + s.card) * h ≤ c ∧ ∀ (O : CoeffRing ℓ) e, ∀ z ∈ selmerModule
    (tateTwist ℓ E O e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : ↑O)), (∀ g ∈ s, z g = 0) → z = 0
  prod_dvd (e : Fin t) : ∏ k ∈ {e}ᶜ, ((cycChar Ω ℓ a⁻¹ ^ e.1).1 - (cycChar Ω ℓ a⁻¹ ^ k.1).1) ∣ ℓ ^ h
  step O j : ∀ z ∈ evenClasses O (.range w) ν (ty j).1, (∀ i < j,
    z (τ i) = 0 ∧ ((ty i).1 = (ty j).1 → z (φ i) = 0)) → ℓ ^ h • z (τ j) = 0
  coboundary (O : CoeffRing ℓ) e : let d g := cycInv ℓ E O g ^ e.1.1 - 1
    2 ^ 2 * d a ^ 2 ∣ (ℓ ^ h : ↑O) ∧ ∀ z ∈ evenClasses O ∅ ν e.1, (∀ j, ty j = e → z (φ j) = 0) →
               ∀ g, d a • (z + z) g = d g • (z + z) a

/-- Q is auxiliary for S and prime to ℓ, ψ is anticyclotomic of modulus Q, and ∑_{P∈Q} v(ψ(σ_P)
− 1) ≤ c, σ_P the tame generator at some place over P. -/
def IsAuxTwist (ψ : Gal(Ω/E) →* PadicAlgCl ℓ) c := IsAuxiliary S Q ∧ IsFromU1 (placesDividing E ℓ) Q
  ψ ∧ ∃ σ, IsNewPlaces 0 ((↑) : Q → _) σ 1 ∧ ∑ k, ellVal (ψ (σ k) - 1) ≤ c

lemma four_dvd_cycChar_sub_one (a : Gal(Ω/E₁)) : 2 ^ 2 ∣ (cycChar Ω ℓ a).1 - 1 := by
  obtain rfl | n := ‹ThePrime ℓ›.out.eq_two_or_odd'; exacts [(pow_dvd_cycChar_sub_iff 2).2
    (cycCharMod_eq_of_dvd (by lia) (cycCharMod_eq_of_isPrimitiveRoot
    (StablyUnram.exists_primitive_root.choose_spec.map_of_injective (algebraMap E₁ _).injective) (by
    simp))), ((PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 (by simpa))).pow 2).dvd]

variable {e} {ν : ℕ} {w₁ : J → FinPlace E} {τ φ : J → Gal(Ω/E)} (hw :
  IsNewPlaces ν w₁ τ φ) {n : Type} [Fintype n]

lemma IsNewPlaces.cycInv_withConjInv {w : J → FinPlace E₁} {τ φ : J → Gal(Ω/E₁)} (hw :
  IsNewPlaces ν w τ φ) (O : CoeffRing ℓ) k : cycInv ℓ _ O (withConjInv τ k) = 1 ∧ ∀ e, (ℓ ^ ν :
  ↑O) ∣ cycInv ℓ _ O (withConjInv φ k) ^ e - 1 := ⟨by
  cases hk : k.2 <;> simp [idOrConjInv, cycInv, hk,
    cycChar_eq_one_of_mem_inertiaAbove (g := τ k.1) (by grind [inertiaAbove, hw k.1])], fun e ↦ by
  simpa using! map_dvd (algebraMap _ O) ((pow_dvd_cycChar_sub_iff (σ := (withConjInv ..)⁻¹ ^ e) ν).2
    (by
      cases hk : k.2 <;> simp_all [idOrConjInv, IsNewPlaces, cycCharMod_prime_pow_eq]))⟩

/-- Let ρ be trivial on inertial elements off S with trivial cyclotomic character. A Selmer
cocycle modulo ℓ^e, allowed to ramify at S and the new places w_j, w̄_j, that vanishes at
the tame generators τ_j and at the τ_j^{−c} is unramified off S. -/
lemma IsNewPlaces.mem_selmerModule_of_tame_eq_zero {w : J → FinPlace E} {τ φ : J → Gal(Ω/E)} (hw :
  IsNewPlaces ν w τ φ) {n : Type} [Fintype n] {ρ : _ →* Matrix n n Λ} {c S T L} (k :
  c ∈ selmerModule ρ T L (QuotSpan (ℓ ^ e : Λ))) (h : ∀ k, c (withConjInv τ k) =
  0) (l : T ⊆ S ∪ .conjClosure (.range w) := by clear * -; intro; simp <;> grind) (hu :
  ∀ g ∈ inertiaAbove Sᶜ, cycChar Ω ℓ g = 1 → ρ g = 1 := by simp +contextual [tateTwist, cycInv]) :
  c ∈ selmerModule ρ S L _ := selmerModule_mono k .rfl fun v
  _ ↦ have ⟨j, o⟩ : ∃ j, v = w j ∨ v = star (w j) := by grind [star_star]
  ((exists_conj_side_detects nsmul_quot_eq_zero _ (hw j).2.2.choose_spec.2 (hw j).1
            (by grind [inertiaAbove, cycChar_eq_one_of_mem_inertiaAbove, IsNewPlaces])
    o).choose_spec.choose_spec.2 c k (h (j, _))).1

variable (ℓ : ℕ) [ThePrime ℓ] {E ι G O O' n σ : Type} [Field E] [UnramCMField E] [CommRing O]
  [CommRing O'] [Fintype n] [Fintype σ] [Monoid G] {q : ℕ} [NeZero q] (h : σ → G →* Multiplicative
  (ZMod q)) (y : σ → O) (hy : ∀ j, y j ^ q = 1) (S S₀ J : Finset (FinPlace E)) (l M : ℕ)

/-- For finite sets S, J of places of E, the union of S, J and the complex conjugate of J. -/
@[grind] noncomputable def unionWithConj := S ∪ (J ∪ J.image star)

/-- The character g ↦ ∏_j y_j^{h_j(g)} of G with values in O, for homomorphisms h_j to ℤ/q and
q-th roots of unity y_j. -/
@[simps] def pointChar : G →* O := ⟨⟨fun g ↦ ∏ j, y j ^ (h j g).toAdd.val, by simp⟩, by
  simp [ZMod.val_add, ← pow_eq_pow_mod, *, pow_add]⟩

/-- For e: O' → O, ρ over O' and y in O^σ, the matrix function g ↦ ∏_j y_j^{h_j(g)}·e(ρ(g)) over
O, exponents taken in [0, q). -/
def twistAtPoint (e : O' →+* O) (ρ : G → Matrix n n _) g :=
  (∏ j, y j ^ (h j g).toAdd.val) • (ρ g).map e

/-- The reduction modulo l^M of a matrix representation ρ over O. -/
noncomputable def reduceModPow (ρ : G →* Matrix n n O) :=
  (algebraMap O (QuotSpan (l ^ M : O))).mapMatrix.1.comp ρ

/-- ρ is balanced up to β: continuous modulo ℓ^M, unramified off S, spanning all matrices, more
than 4n + 2 residues, coboundaries obeying L; γ, inertial at S off ℓ, and γ^{−c} act by one
scalar s with s ± 1 units; some g, g^{−c} act by scalars α, α', and for a ∣ ℓ^M, Σ_{v∈S}
(least length of `localCocycles`) + n·v(α − cyc(g^c)α') ≤ (|S| + f)·length (O/a)^n + β,
f the number of infinite places of E. -/
structure IsBalanced [PadicIntegerRing O ℓ] (ρ : Gal(Ω/E) →* Matrix n n O) (L γ β M) where
  isLocallyConstant : IsLocallyConstant (reduceModPow ℓ M ρ)
  unramified : ∀ g ∈ inertiaAbove Sᶜ, ρ g = 1
  span_eq_top : span O (.range ρ) = ⊤
  scalar_inertia : γ ∈ inertiaAbove (S \ placesDividing E ℓ) ∧
    ∃ s : O, (ρ (conjGal γ)⁻¹ = s • 1 ∧ ρ γ = s • 1) ∧ IsUnit (s + 1) ∧ IsUnit (s - 1)
  lt_card_residue : 4 * card n + 2 < .card (IsLocalRing.ResidueField O)
  coboundary_mem (a : O) (b : n → QuotSpan a) : (ρ · • b - b) ∈ obeying (O := O) L _
  local_length_le : ∃ g α α', (ρ g = α • 1 ∧ ρ (conjGal g)⁻¹ = α' • 1) ∧ ∀ a : O, a ∣ ℓ ^ M →
    ∑ v ∈ S, (⨅ A : {A // IsPlaceOver A v},
    length O (localCocycles ρ L A.1 (QuotSpan a))) + card n * addVal O (α - cycCharIn O Ω
    ℓ (conjGal g) * α') ≤ (S.card + numInfPlaces E) • length O (n → QuotSpan a) + β

/-- An auxiliary set J with anticyclotomic characters h_w modulo ℓ^N, Frobenii φ_v and slopes,
and P₀ ∈ J with φ_{P₀} ∈ W; for v ≠ P₀, h_w(φ_v) is 1 if w = P₀, else 0; U_i holds at φ_v,
φ_v^{−c} where slope i is nonzero. -/
structure IsPencil (U : ι → _ → Prop) (W : Set _) (N P₀ J) (x : _ →
  AuxPrimeData E (ℓ ^ N) × (ι → O)) where
  auxiliary : IsAuxiliary S₀ J
  helper_mem : P₀ ∈ J
  anticyclotomic : ∀ v ∈ J, IsAnticyclotomicAt (placesDividing E ℓ) v (x v).1
  char_frob : ∀ v ∈ J, v ≠ P₀ → ∀ w ∈ J, (x w).1.h (x v).1.φ = ite (w = P₀) (.ofAdd 1) 1
  helper_near : (x P₀).1.φ ∈ W
  frob_trivial : ∀ v ∈ J, ∀ i, (x v).2 i ≠ 0 → ∀ b, U i (idOrConjInv b (x v).1.φ)

/-- The ties of row i: the relations c(γ_v) = t_{v,i}·c(φ_v) and c(γ_v^{−c}) =
t_{v,i}·c(φ_v^{−c}) for v in J. -/
def tieRelations (x : FinPlace E → AuxPrimeData E q × (ι → O)) i := range fun p : J × _ ↦
  (.single (idOrConjInv p.2 (x p.1).1.γ)
  1 - .single (idOrConjInv p.2 (x p.1).1.φ) ((x p.1).2 i • 1) : _ →₀ Matrix n n O)

lemma idOrConjInv_mem_inertiaAbove {A : ClosurePlace} {P S τ} (hA : IsPlaceOver A P) (hτ :
  τ ∈ inertiaGroup Gal(Ω/E) A) (h : P ∈ S ∧ star P ∈ S) b : idOrConjInv b τ ∈ inertiaAbove S :=
  b.rec ⟨_, h.2, _, hA.conjPlace_star, inv_mem hτ.conjPlace_conjGal⟩ ⟨P, by tauto⟩

attribute [local simp] Quotient.forall funext_iff mul_assoc

/-- Given m ≠ 0, a neighbourhood W of 1 and S finite, there are finitely many coordinates γ and
R ⊇ mΛ^ι such that, for every Λ-module B killed by m with W acting trivially on B^n,
evaluation at γ bijects `selmerModule` onto the w in B^ι killed by R. -/
lemma exists_corepresenting_coords {E n Λ : Type} [Field E] [EmbeddedNumberField E] [Fintype n]
  [CommRing Λ] (m : ℕ) [NeZero m] (ρ : Gal(Ω/E) → Matrix n n Λ) {W} (hW : W ∈ nhds 1) {S} (hS :
  S.Finite) L : ∃ (ι : Type) (_ : Fintype ι), ∃ γ R, (∀ v : ι → Λ, m • v ∈ R) ∧
  ∀ (B : Type) [AddCommGroup B] [Module Λ B], (∀ b : B, m • b = 0) → (∀ g ∈ W, ∀ b : n → B,
  ρ g • b = b) → BijOn (↿· ∘ γ) (selmerModule ρ S L B).carrier
  {w | R ≤ (Fintype.linearCombination Λ w).ker} := (is_nonarchimedean _ hW).rec fun U hU ↦ by
  choose V hV using is_nonarchimedean _ ((selmerZ1.finite_unramified_cocycles (.funModule (.of
    (.trivial ℤ _ (ZMod m))) U) hS).eventually_all.2 fun z h ↦ (h.1.1.1 {_} (by simp)).mem_nhds rfl)
  use (_ ⧸ V.1) × n, .ofFinite _, .map (·.out) id, .span Λ (image2 (relEval _ · (Pi.single
    ⟨QuotientGroup.mk ·, ·⟩ 1)) (cocycleRels ρ ∪ (.single · 1) '' inertiaAbove Sᶜ ∪ L) univ ∪ range
    (m • ·)), (subset_span <| .inr ⟨·, rfl⟩), fun _ _ _ hm hρ ↦ ?_
  simp [span_le, -relEval, -mem_union, ← comp_mem_obeying_iff, -nsmul_eq_mul, *]
  refine InvOn.bijOn ⟨?F, by simp [LeftInvOn, (↿·)]⟩ (fun _ H ↦ (?F H ▸ H.1 :))
    fun w ↦ (⟨·, .of_discrete w.curry⟩)
  exact fun c H ↦ funext₂ fun x i ↦ sub_eq_zero.1 (eq_zero_of_forall_hom_eq_zero
    ((bijective_ofZMod_comp hm).2.forall.2 fun χ ↦ by simpa using! congr(ofZMod m ($(hV
    (QuotientGroup.eq.1 (out_eq' ⟦x⟧).symm) (fun g ↦ Quotient.lift (fun a ↦ χ ((_ - c a⁻¹) i))
    (by rintro _ _ ⟨u, rfl⟩; simp [Subgroup.smul_def, mem_selmerModule_iff.1 H, hρ _ (hU
    (inv_mem u.2))])) ⟨⟨continuous_pi (Quotient.ind ((H.2.comp (χ <| · i - _)).continuous.comp <|
    continuous_const_mul ·⁻¹)), by simp⟩, by simp_all [mem_selmerModule_iff.1 H]⟩) ⟦x⁻¹⟧))))
