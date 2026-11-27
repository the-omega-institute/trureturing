/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Adeles/CoprimeValuation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Adeles/CoprimeValuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Adeles.CoprimeValuation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Adeles/CoprimeValuation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.Base
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Places, completions, adeles, integral adeles, maps under field embeddings, CM
conjugation. -/

noncomputable section

open Ideal _root_.IsDedekindDomain Set Classical Filter IsLocalRing NumberField RestrictedProduct
  Valued WithZero WithZeroTopology Ideal.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  UniformSpace.Completion adicCompletion

/-- A choice, for each infinite place w of E, of a complex embedding Φ w of E that induces w. -/
class PlaceEmbedding (E : Type*) [Field E] where
  Φ : _ → E →+* ℂ
  mk_Φ w : InfinitePlace.mk (Φ w) = w

export PlaceEmbedding (Φ mk_Φ)

attribute [simp] mk_Φ

instance (priority := low) (E : Type*) [Field E] : PlaceEmbedding E :=
  ⟨_, InfinitePlace.mk_embedding⟩

/-- E is a CM number field equipped with a CM type: for each infinite place w of E, a chosen
complex embedding of E that induces w. -/
class CMType (E : Type*) [Field E] extends NumberField E, IsCMField E, PlaceEmbedding E

/-- The set of finite places of E, that is, nonzero prime ideals of its ring of integers. -/
abbrev FinPlace (E : Type*) [Field E] := HeightOneSpectrum (𝓞 E)

/-- The ring of finite adeles of the number field E. -/
abbrev 𝔸f (E : Type*) [Field E] [NumberField E] := FiniteAdeleRing (𝓞 E) E

/-- The ring ℂ^f × 𝔸_f, one copy of ℂ for each infinite place of E times the finite adeles: the
adele ring of E when E is totally complex. -/
abbrev 𝔸 (E : Type*) [Field E] [NumberField E] := (InfinitePlace E → ℂ) × 𝔸f E

variable {E : Type*} [Field E] [NumberField E] (w : FinPlace E) {K L : Type*} [Field K]
  [NumberField K] [Field L] [NumberField L] (f : K →+* L) {w' : FinPlace K} (x : 𝓞 K) (x : K)

/-- The diagonal embedding of E in its adeles, given at the infinite places by the chosen embeddings
Φ w. -/
@[simps! apply_fst apply_snd] def toAdele [PlaceEmbedding E] : E →+* 𝔸 E :=
  .prod (.pi Φ) (algebraMap ..)

instance [PlaceEmbedding E] : Coe E (𝔸 E) := ⟨toAdele⟩

instance : Coe E (𝔸f E) := ⟨algebraMap ..⟩

/-- The completion E_w of E at the finite place w. -/
abbrev LocField := w.adicCompletion E

/-- The ring of integers of the completion E_w of E at the finite place w. -/
abbrev LocInt := w.adicCompletionIntegers E

instance : CommSemiring (LocInt w) := CommRing.toCommSemiring

instance : @IsLocalRing (LocInt w) CommRing.toCommSemiring.toSemiring := inferInstance

/-- The residue field of the completion E_w of E at the finite place w. -/
@[instance_reducible] def ResField := ResidueField (LocInt w) deriving Field, Algebra (𝓞 E)

/-- The absolute norm of the prime ideal w, that is, the order of its residue field. -/
abbrev FinPlace.q := w.1.absNorm

@[simp] lemma FinPlace.one_lt_q : 1 < w.q := HeightOneSpectrum.one_lt_absNorm w

@[simp] lemma FinPlace.q_bounds : 0 < w.q - 1 ∧ w.q ≠ 0 ∧ 1 ≤ w.q ∧ 0 < w.q := by grind [one_lt_q]

/-- A chosen uniformiser of the completion of E at the finite place w. -/
def uniformizer :=
  Units.mk0 (w.valuedAdicCompletion_surjective E (exp (-1))).choose (by grind [exp_pos])

@[simp] lemma v_uniformizer : v (uniformizer w).1 = exp (-1) := by grind [uniformizer, Units.mk0]

/-- The ring homomorphism sending a finite adele to its component in E_w. -/
def evalAt : 𝔸f E →+* LocField w := evalRingHom (fun v ↦ LocField v) w

@[simp] lemma evalAt_apply x : evalAt w x = x w := rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The map sending a in E_w to the finite adele with component a at w and 0 elsewhere, a ring
homomorphism that does not preserve 1. -/
def singleAdele : LocField w →ₙ+* 𝔸f E :=
    ⟨⟨.single LocInt w, (Subtype.ext <| Pi.single_mul w · ·)⟩, single_zero .., single_add _ _⟩

@[simp] lemma singleAdele_same x : singleAdele w x w = x := dite_eq_left rfl

@[simp] lemma singleAdele_of_ne {v w : FinPlace E} (h : v ≠ w) x : singleAdele w x v = 0 :=
  dite_eq_right h

/-- The subring Ô of finite adeles of E that are integral at every finite place. -/
def Ô (E : Type*) [Field E] [NumberField E] := ⨅ w : FinPlace E, (LocInt w).1.comap (evalAt w)

lemma mem_Ô {x} : x ∈ Ô E ↔ ∀ w, v (x w) ≤ 1 := Subring.mem_iInf

/-- Reduction modulo w: the ring homomorphism from the integral finite adeles to the residue
field at w. -/
def reduceAt : Ô E →+* ResField w :=
  (residue _).comp (((evalAt w).domRestrict _).codRestrict _ (mem_Ô.1 ·.2 w))

instance : MeasurableSpace (LocField w) := borel _

instance : BorelSpace (LocField w) := ⟨rfl⟩

instance : MeasurableSpace (𝔸f E) := borel _

instance : BorelSpace (𝔸f E) := ⟨rfl⟩

/-- The structure of ring with involution on a commutative ring R given by a ring endomorphism
whose square is the identity. -/
abbrev starRingOfInvolution {R} [CommRing R] (star : R →+* R) (star_involutive :
  (⇑star).Involutive) : StarRing R := by refine' { star, .. } <;> grind

@[local simp] lemma v_algebraMap_eq_valuation : v (algebraMap K (LocField w') x) =
  w'.valuation K x := valued_coe ..

lemma mem_LocInt {x} : x ∈ LocInt w' ↔ v x ≤ 1 := .rfl

variable {w : FinPlace K} (x : 𝓞 K)

lemma v_algebraMap_eq_intValuation : v (algebraMap K (LocField w) x) =
  w.intValuation x := by simp [valuation_of_algebraMap]

lemma v_algebraMap_eq_one {x} (h : x ∉ w.1) : v (algebraMap K (LocField w) x) = 1 := by simpa

section

@[local fun_prop] lemma continuous_v : Continuous (v : LocField w → _) :=
    continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective K)

lemma finite_natCast_mem n [NeZero n] : {v : FinPlace K | Nat.cast n ∈ v.1}.Finite := by
  simp [← dvd_span_singleton, finite_factors, NeZero.ne]

/-- For f: K → L and a finite place w of L, the finite place of K below w: the preimage under f
of the prime ideal w. -/
def FinPlace.comap (w : FinPlace L) : FinPlace K := let := f.toAlgebra; w.under _

variable {u} {w : FinPlace L} (h : w.comap f = u) (x : K) [IsCMField E]

/-- For an extension L/K, the finite place of K below the finite place w of L. -/
abbrev FinPlace.below K [Field K] [Algebra K L] w := comap (algebraMap K L) w

/-- Two continuous maps to a Hausdorff space that agree on the image of a map with dense range
are equal. -/
lemma DenseRange.eq {X Y ι} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {e : ι → X}
  (D : DenseRange e) {f g : X → Y} (h : ∀ a, f (e a) = g (e a) := by aesop) (a : Continuous f := by
  fun_prop) (b : Continuous g := by fun_prop) x : f x = g x := D.induction_on x (isClosed_eq a b) h

/-- For f: K → L and a finite place w of L above u, the continuous ring homomorphism K_u → L_w
extending f. -/
def locMap := let := f.toAlgebra; have := LiesOver.mk congr($h.1).symm
  (equiv L w).symm.toRingHom.comp ((mapRingHom _ (uniformContinuous_algebraMap_liesOver K L
    ..).continuous).comp (equiv K u).toRingHom)

@[fun_prop] lemma continuous_locMap :
    Continuous (locMap f h) := continuous_induced_rng.2 (continuous_map.comp (by fun_prop))

@[simp] lemma locMap_algebraMap : locMap f h (algebraMap K _ x) = algebraMap L _ (f x) := by
  simp [locMap, -mapRingHom_apply]; erw [mapRingHom_coe]; rfl

attribute [irreducible] locMap

lemma exists_v_locMap_eq_pow : ∃ e ≠ 0, ∀ x, v (locMap f h x) = v x ^ e := let := f.toAlgebra
            have := LiesOver.mk congr($h.1).symm; ⟨_, (w.1.ramificationIdx_pos (𝓞 K)).ne',
              (u.denseRange_algebraMap K).eq (by simp [valuation_liesOver L]; tauto)⟩

@[simp] lemma v_locMap_le_one {x} : v (locMap f h x) ≤ 1 ↔ v x ≤ 1 := by
  grind [exists_v_locMap_eq_pow f h, pow_le_one_iff]

lemma isEquiv_comap_locMap : (v.comap (locMap f h)).IsEquiv v :=
  Valuation.isEquiv_of_val_le_one (by simp)

lemma v_locMap_eq_of_isUnit_log (s : ∃ z, IsUnit (v (locMap f h z)).log) x : v (locMap f h x) =
  v x := by cases exists_v_locMap_eq_pow f h; simp_all [Int.isUnit_iff]

lemma v_locMap_eq_of_surjective (s : (⇑f).Surjective) : ∀ x, v (locMap f h x) = v x :=
  v_locMap_eq_of_isUnit_log f h
  (((w.valuation_surjective L).comp s (exp 1)).imp' (algebraMap ..) (by aesop))

lemma tendsto_place_comap_cofinite :
  Tendsto (FinPlace.comap f) cofinite cofinite := let := f.toAlgebra
  .cofinite_of_finite_preimage_singleton (map_ne_bot_of_ne_bot ·.3 |> finite_factors |>.subset
                           fun _ ↦ (· ▸ dvd_iff_le.2 map_comap_le))

/-- For an embedding f: K → L of number fields, the induced ring homomorphism from the finite
adeles of K to those of L; it gives base change and the Galois action. -/
def adeleMap : 𝔸f K →+* 𝔸f L := mapAlongRingHom LocField LocField _ (tendsto_place_comap_cofinite f)
  (fun _ ↦ locMap f rfl) (by simp [MapsTo, mem_LocInt])

variable (K L) in
/-- For an extension of number fields L over K, the inclusion of the finite adeles of K in those
of L. -/
abbrev finAdeleIncl [Algebra K L] := adeleMap (algebraMap K L)

lemma adeleMap_apply x : adeleMap f x w = locMap f h (x u) := by aesop

@[fun_prop] lemma continuous_adeleMap : Continuous (adeleMap f) := by apply
  mapAlong_continuous <;> simp [tendsto_place_comap_cofinite, MapsTo, mem_LocInt, continuous_locMap]

@[simp] lemma adeleMap_algebraMap : adeleMap f x = f x := by ext1; apply locMap_algebraMap

instance : StarRing (𝓞 E) :=
  starRingOfInvolution (IsCMField.ringOfIntegersComplexConj E) (by aesop_cat)

@[simp, norm_cast] lemma coe_star_ringOfIntegers (x : 𝓞 E) : star x = star x.val := rfl

@[simp] lemma map_star_complex (φ : E →+* ℂ) x :
    φ (star x) = star (φ x) := IsCMField.complexEmbedding_complexConj ..

lemma map_star_CM [IsCMField K] [IsCMField L] x : f (star x) = star (f x) :=
    (Φ ofNonempty).injective ((map_star_complex (.comp ..) x).trans (by simp))

instance : InvolutiveStar (FinPlace E) :=
    { star := comap (starRingEnd _) star_involutive.surjective, star_involutive w := by aesop }

/-- The finite place w of the CM field E is split over the maximal real subfield: it differs
from its complex conjugate. -/
abbrev FinPlace.IsSplit (w : FinPlace E) := star w ≠ w

variable {u w : FinPlace E} (h : star u = w)

@[simp] lemma mem_star_place {x} : x ∈ (star w).1 ↔ star x ∈ w.1 := .rfl

variable (E) in
/-- The hypothesis on a CM field E, called stably unramified, that E contains a primitive root
of unity of order 5040 = 7!. -/
class StablyUnram [IsCMField E] where exists_primitive_root : ∃ ζ : E, IsPrimitiveRoot ζ 5040

/-- If the CM field E contains a primitive 5040-th root of unity, then O_E contains i with i² =
−1, ī = −i, and ω with ω + ω̄ = 1, ωω̄ = 2. -/
lemma StablyUnram.exists_i_c₀ [h : StablyUnram E] : ∃ i ω : 𝓞 E, i * i = -1 ∧ star i = -i ∧
  ω + star ω = 1 ∧ ω * star ω = 2 := have ⟨y, z⟩ : ∃ y, IsPrimitiveRoot y 28 :=
    ⟨_ ^ 180, h.1.choose_spec.toInteger_isPrimitiveRoot.pow (by simp) rfl⟩
  have g a := (z.pow_of_dvd (p := a) · · |>.geom_sum_eq_zero)
  ⟨y ^ 7, y ^ 2 - y ^ 4 - y ^ 8, by
  obtain := g 14, g 4, (congr($(IsCMField.unitsComplexConj_torsion E
    ⟨_, (z.isUnit_unit (by simp)).isOfFinOrder nofun⟩).1 * y) : star y * y = _)
  simp [Finset.sum_range_succ] at *
  grind⟩

lemma StablyUnram.exists_isUnit_sub_star [StablyUnram E] : ∃ y : 𝓞 E, IsUnit (y - star y) :=
  exists_i_c₀.elim fun i ⟨ω, _⟩ ↦ ⟨i * ω, .of_mul_eq_one (-i) (by grind [star_mul])⟩

/-- For finite places u, w with ū = w, the homomorphism E_u → E_w of completions induced by
complex conjugation. -/
def conjLoc := locMap (starRingEnd E) (star_eq_iff_star_eq.1 h)

@[simp] lemma v_conjLoc x : v (conjLoc h x) = v x :=
  v_locMap_eq_of_surjective _ _ starRingAut.surjective x

@[simp] lemma valuation_star (w : FinPlace E) x : (star w).valuation E (star x) = w.valuation E
  x := by erw [← v_algebraMap_eq_valuation x, ← v_conjLoc rfl, locMap_algebraMap]; aesop

end

lemma Nat.Coprime.valuation_eq_one {Ω} [Field Ω] {B : ValuationSubring Ω} {p q : ℕ} (hq :
  p.Coprime q) (h : B.valuation p < 1) : B.valuation q = 1 := (B.valuation_eq_one_iff q).1
  (by_contra (IsPrime.notMem_of_isCoprime_of_mem hq.cast (B.coe_mem_nonunits_iff.1 h)))
