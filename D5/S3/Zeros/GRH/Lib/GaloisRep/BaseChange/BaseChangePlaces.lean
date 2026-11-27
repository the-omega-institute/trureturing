/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangePlaces
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangePlaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.BaseChange.BaseChangePlaces. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/BaseChange/BaseChangePlaces.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.OrbitClassSum
import D5.S3.Zeros.GRH.Lib.ClassField.Places.AdeleNorm
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local matching)
(known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: A totally complex number field with a conjugation for all embeddings is CM. E[X]/P is CM
when roots have constant modulus; its finite adeles as polynomials. Cyclic prime-degree CM extension
with test character; compatible CM types; matched places. Base change map and Galois action on
finite adelic points of unitary groups. Places above a set, adelic matched pairs, basic
compatibilities of base change maps. -/

open NumberField InfinitePlace Module Fintype Polynomial AdjoinRoot Algebra ComplexConjugate

/-- Let L be a number field extending a totally complex field E. If every x ∈ L has a y ∈ L with
φ(y) equal to the complex conjugate of φ(x) for all embeddings φ : L → ℂ, then L is a CM
field. -/
lemma isCMField_of_forall_exists_conj E {L} [Field E] [IsTotallyComplex E] [Field L] [Algebra E L]
    [NumberField L] (H : ∀ x, ∃ y, ∀ φ : L →+* ℂ, φ y = star (φ x)) : IsCMField L :=
  have := isTotallyComplex_of_algebra E L; {is_quadratic := ⟨by
    let K := maximalRealSubfield L
    simpa [← sum_mult_eq, card_of_bijective (f := (·.comap K.subtype)) ⟨fun v w h ↦
      InfinitePlace.ext v w fun x ↦ (H x).rec fun y
      e ↦ by simpa [↓comap_apply, ← norm_embedding_eq, e, ← sq] using congr($h ⟨x * y,
      (by simp [e ·, field])⟩), comap_surjective⟩] using finrank_mul_finrank ℚ K L⟩}

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {P : E[X]} [h : Fact (Irreducible P)]

instance : NumberField (AdjoinRoot P) := have := (powerBasis h.1.ne_zero).finite
  of_module_finite E _

/-- Let P be monic irreducible over the CM field E, all complex roots satisfying r r̄ = ν ∈ ℚ. Then
L = E[X]/(P) is CM, θθ̄ = ν, and X ↦ θ presents 𝔸_{L,f} as 𝔸_{E,f}[X]/(P), compatibly with L and
conjugation. -/
lemma adjoinRoot_cm_presentation (hm : P.Monic) (ν : ℚ) (hν : ∀ᵉ (σ) (r ∈ (P.map σ).roots),
  r * star r = (ν : ℂ)) {ε} (hε : ε = aeval (root P : 𝔸f (AdjoinRoot P))) {j} (hj : j =
  algebraMap E (𝔸f E)) : ∃ _ : IsCMField (AdjoinRoot P), root P * star (root P) = ν ∧
  (⇑ε).Surjective ∧ (∀ q, ε q = 0 ↔ P.map j ∣ q) ∧ (∀ q, ε (q.map j) = AdjoinRoot.mk P q) ∧ ∀ c q,
  AdjoinRoot.mk P c = star (root P) → ε ((q.map conj).comp (c.map j)) = star (ε q) := hε ▸
  have hr φ := hν (.comp φ (of P)) (φ (root P)) (by simp [← map_map, hm.ne_zero, eval_map])
  have := isCMField_of_forall_exists_conj E (induction_on P · (⟨·.map conj |>.aeval (ν / root P), by
    simp [← aeval_eq, aeval_eq_sum_range, smul_def]
    congr! 3; apply map_star_complex (.comp ..); grind [starRingEnd_apply]⟩))
  have f q := by simp [*, ← aeval_eq, aeval_eq_sum_range, smul_def, algebraMap_eq_finAdeleIncl]
  let A := IsAdjoinRootMonic.mkOfAdjoinEqTop' (PowerBasis.adjoin_gen_eq_top ⟨_, _, adeleBasis
    (powerBasis' hm).3, by simp [adeleBasis]⟩)
  ⟨this, canonicalEmbedding_injective _ (by aesop), A.1.2, (eq_of_monic_of_dvd_of_natDegree_le A.2
    (hm.map j) (A.mem_ker_map.1 (by aesop)) (by simp [↓PowerBasis.natDegree_minpoly])).substr
    @A.mem_ker_map, f, fun _ ↦ (·.induction_on' (by aesop)
    (by simp_all [algebraMap_eq_finAdeleIncl, ← adeleMap_star]; tauto))⟩

variable {E : Type} (E' : Type) [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E']
  [Algebra E E'] (μ : outParam ((𝔸f E)ˣ →* ℂˣ))

/-- A step: E stably unramified, E' CM and Galois of prime degree over E with an integer of
trace 1, μ of open kernel, trivial on E^×, with μ(zz̄) = 1 iff z ∈ E^×·Nm(finite ideles of
E'). -/
class IsStep extends StablyUnram E, NumberField E', IsCMField E', IsGalois E E',
    Fact (Module.finrank E E').Prime where
  isOpen_ker : μ.ker.IsOpen
  apply_principal x : μ (principalIdele x) = 1
  apply_norm_eq_one_iff z : μ (z * star z) = 1 ↔ ∃ x y, z =
    principalIdele x * .map (adeleNorm E E') y
  exists_trace_eq_one : ∃ c : 𝓞 E', Algebra.trace E E' c = 1

/-- A CM type of L that restricts to the given CM type of K: the embedding chosen at a place
extends the one chosen at the place below. -/
class CMOver K L [Field K] [Field L] [Algebra K L] [PlaceEmbedding K] extends CMType L where
  mem_type_iff σ : σ = Φ (.mk σ) ↔ σ.comp (algebraMap K L) =
    PlaceEmbedding.Φ (.comap (.mk σ) (algebraMap ..))

/-- The group of finite ideles of E' whose norm to E is killed by μ. -/
noncomputable abbrev normKer := (μ.comp (Units.map (adeleNorm E E'))).ker

/-- Matched place: μ is trivial on E_w^×, and every place of E' above w has the norm of w and is
moved by every σ ≠ 1. -/
def IsMatched w := (∀ x, μ (locIdele w x) = 1) ∧ ∀ u :
    FinPlace E', u.below E = w → u.q = w.q ∧ ∀ σ ≠ (1 : Gal(E'/E)), u.comap σ ≠ u

variable {E E' : _} [Field E] [NumberField E] [Field E'] [NumberField E']
  [NumberField.IsCMField E'] [Algebra E E'] {n} [Fintype n] (σ : Gal(E'/E))

omit [NumberField E] [NumberField E'] [NumberField.IsCMField E'] in
@[simp] lemma below_comap (u : FinPlace E') :
    (u.comap σ : FinPlace E').below E = u.below E := congr(u.comap $σ.toAlgHom.comp_algebraMap)

omit [NumberField.IsCMField E'] in
lemma bijective_pow_gal [IsGalois E E'] [h : Fact (Module.finrank E E').Prime] {σ} :
    σ ≠ 1 → Function.Bijective (σ ^ ·.1 : Fin (Module.finrank E E') → Gal(E'/E)) := by
  grind [Nat.bijective_iff_injective_and_card, IsGalois.card_aut_eq_finrank, Nat.card_fin,
    orderOf_eq_prime, pow_card_eq_one', Function.Injective, pow_inj_mod, Nat.mod_eq_of_lt]

/-- The homomorphism from the finite adelic unitary group over E to the one over E' induced by
the inclusion of finite adeles. -/
noncomputable def baseChangeGf [NumberField.IsCMField E] :
    Gf E n →* Gf E' n := U.map _ (adeleMap_star (algebraMap ..))

/-- The action of σ in Gal(E'/E) on the finite adelic unitary group over E', entry by entry. -/
noncomputable abbrev galoisGf : Gf E' n →* Gf E' n := U.mapEnd (adeleMap_star σ)

open Matrix Valued Gf IsGalois
variable {E E' n : _} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n] (σ :
  Gal(E'/E)) (μ : (𝔸f E)ˣ →* ℂˣ) {w : FinPlace E} {u : FinPlace E'} (S : Set (FinPlace E)) (g :
  Gf E n)

variable (E') in
/-- The set of finite places of E' lying above a place of S or above the complex conjugate of a
place of S. -/
def placesAbove := .below (L := E') E ⁻¹' S.conjClosure

omit [CMType E] in
lemma atPlace_galoisGf (g : Gf _ n) {v} h : (galoisGf σ g).atPlace u =
  .map (locMap σ h) (g.atPlace v) := h ▸ rfl

/-- The condition `IsMatchingPair` for σ on the finite adeles of E', degree [E':E], the idempotent
of the places above S ∪ S̄, and the ideles killed by μ∘Nm. -/
abbrev IsMatchingPairAbove := IsMatchingPair (adeleMap_star σ) (finrank E E')
  (idem (placesAbove _ S)) (normKer E' μ) (baseChangeGf : Gf E n → _)

lemma continuous_baseChangeGf : Continuous (baseChangeGf : Gf E n → Gf E' n) := U.continuous_map

lemma atPlace_baseChangeGf : (baseChangeGf g).atPlace u =
  .map (locMap _ rfl) (g.atPlace (u.below E)) := rfl

lemma atPlace_sub_one_apply i j : ((g.atPlace w).1 - 1) i j = (g.1.1 - 1) i j w := by aesop

variable {σ μ S g}

@[simp] lemma star_mem_placesAbove : star u ∈ placesAbove _ S ↔
  u ∈ placesAbove _ S := by simp [placesAbove, below_star]; tauto

omit [Algebra E E'] in
lemma locMap_mem_Kw {f} (h : u.comap f = w) {g} : .map (locMap f h) g ∈ intGL n v.integer
    ↔ g ∈ intGL n v.integer := by simp [mem_intGL, ← map_inv, v.mem_integer_iff]

lemma baseChangeGf_mem_Kf : baseChangeGf g ∈ Kf E' n ↔
  g ∈ Kf .. := by simp [mem_Kf, baseChangeGf, U.map]

lemma baseChangeGf_mem_supportedOn : g ∈ supportedOn n S → baseChangeGf g ∈ supportedOn n
  (placesAbove E' S) := by simp_all [atPlace_baseChangeGf, placesAbove]

lemma idem_smul_eq_iff_mem_trivialOn : idem S • g.1.1 = idem S • 1 ↔
  g ∈ trivialOn n S := by simp +contextual [Units.ext_iff,
  atPlace, ← Matrix.ext_iff, DFunLike.ext_iff, idem_apply, apply_ite, ite_prop_iff_and]; grind

lemma trivialOn_le_localLevel {K} : trivialOn n S ≤ localLevel n S K := by aesop_cat

lemma adeleMap_idem_placesAbove : adeleMap σ (idem (placesAbove E' S)) =
  idem (placesAbove E' S) := by aesop (add simp [adeleMap_apply, idem_apply, placesAbove])

omit [CMType E'] in
lemma IsStep.isClopen_normKer (hμ : IsStep E' μ) : IsClopen (normKer E' μ).carrier :=
  OpenSubgroup.isClopen ⟨_, hμ.6.preimage_of_continuous⟩

omit [CMType E'] in
lemma IsStep.exists_gal_ne_one (hμ : IsStep E' μ) : ∃ σ : Gal(E'/E), σ ≠ 1 :=
  Fintype.exists_ne_of_one_lt_card (by simpa [← card_aut_eq_finrank] using hμ.out.one_lt) 1

lemma adeleMap_pow_finrank_eq_one [IsGalois E E'] : adeleMap (σ : E' →+* E') ^ finrank E
  E' = 1 := by ext; simp [adeleMap_gal_pow, ← card_aut_eq_finrank]; erw [adeleMap_id]
