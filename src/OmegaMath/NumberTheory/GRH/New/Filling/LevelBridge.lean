import OmegaMath.NumberTheory.GRH.New.Filling.Setup
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: dictionaries between two encodings of the same objects.

This file: Dictionary between rational, finite adelic and real coordinates of the filling record.
Form, level unit, additive character and level group of the record in local terms. -/

noncomputable section

namespace Filling

open NumberField Matrix Complex Circle Finset Real Prod intGL IsHermUnit

section

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} {R R' : Type}
  [CommRing R] [CommRing R'] (f : R →+* R')

attribute [local simp] BlockTriangular coe_ratToFin GT unipotentChar toLatBasis h termPosition
  val_toBesselH_apply_coe mul_assoc fourierChar_apply inclHFin funext_iff

attribute [-simp] Sum.forall

attribute [local aesop simp] selfDualChar gIdele splitGram middleGram latMiddleGram
  besselLatticeBasis FI.level

lemma map_splitGram_latMiddle : (S.latMiddle R).splitGram.map f =
  (S.latMiddle _).splitGram := by aesop

lemma _root_.Membership.mem.map_mem_unitriangularOn {r h} {H : Subgroup (GL 𝔰.BesselIndex _)} {γ} :
    γ ∈ (agreeWithOneOn r _ h).subgroupOf H → .map f γ.1 ∈ agreeWithOneOn r _ h := by aesop

instance : IsHermUnit (S.ratMiddle E) := ⟨by aesop, by simp [isUnit_iff_isUnit_det, middleGram]⟩

variable {c s c' t c'' x} {γ δ : S.G E} (u)

lemma toLatBasis_mem_besselU : S.toLatBasis x ∈ besselU ↔ x ∈ besselU := ⟨(by
  simpa using! conj_mem_unitriangular (d := S.latBasis⁻¹) (by aesop) ·.out),
  (conj_mem_unitriangular (by aesop) ·.out)⟩

@[simp] lemma ratToFin_mem_besselU : S.ratToFin γ ∈ besselU ↔ γ ∈ besselU :=
  toLatBasis_mem_besselU.trans (by simp [mem_besselU, ← algebraMap.coe_inj E (𝔸f E)]; rfl)

lemma inclHFin_mem_besselH k : S.inclHFin k ∈ besselH := by simp [besselLatticeBasis, Sum.forall]

lemma range_inclHFin : S.inclHFin.range = besselH := le_antisymm (fun _ ⟨k, e⟩ ↦
  e ▸ inclHFin_mem_besselH k) fun _ h ↦ .imp (fun _ ↦ S.toLatBasis.eq_symm_apply.1 ∘ .symm)
  (exists_toBesselH_eq (by apply mul_mem (mul_mem _ h.out) <;> aesop) (by simp [← piBar_mul_star]))

lemma ratToFin_toBesselH γ : S.ratToFin (toBesselH _ _ γ) =
  S.inclHFin (stdEmbFin γ) := by ext; simp [stdSpace_embFin γ]

/-- For a class c with representative h_c, the finite adelic matrix h_c·`Filling.latBasis`, whose
columns form a basis of the lattice h_cΛ₀ in rational coordinates. -/
def classBasis (c : S.Classes) := (toBesselH _ ↑S.N c.out).1 * S.latBasis

lemma coe_termPosition c c' γ : (S.termPosition c c' γ).1 =
  (classBasis c)⁻¹ * .map (algebraMap E _) γ * classBasis c' := by simp [classBasis]

lemma _root_.Membership.mem.termPosition_mem_besselU c : γ ∈ besselU → S.termPosition c c γ ∈
  besselU := (besselS_le_normalizer_besselU (mem_unitriGroup_of_mem_floorGroup
  (inv_mem (inclHFin_mem_besselH _))) _).1 ∘ ratToFin_mem_besselU.2

lemma termsOver.mul : γ ∈ S.termsOver c s c' → δ ∈ S.termsOver c' t c'' →
  γ * δ ∈ S.termsOver c (s * t) c'' | ⟨k, _⟩ => .imp' (k * ·) (by aesop)

lemma termsOver.inv : γ ∈ S.termsOver c s c' → γ⁻¹ ∈ S.termsOver c' s⁻¹ c := .imp' (·⁻¹) (by aesop)

@[local simp] lemma simpleRootSum_adelicToFin : simpleRootSum (S.adelicToFin u) =
  (simpleRootSum u).2 := by
  simp [-sum_add_distrib, simpleRootSum, snd_sum, adelicToFin, besselLatticeBasis, mul_apply,
    U.map]; congr with a
  refine a.succ.lastCases ?_ ?_ <;> simp

@[simp] lemma simpleRootSum_ratToAdelic : simpleRootSum (S.ratToAdelic u) = simpleRootSum u :=
  .symm (map_sum ..)

@[simp] lemma norm_selfDualChar : ‖S.selfDualChar x‖ = 1 := norm_coe _

lemma _root_.Membership.mem.ratToInf_mem_unitriangularOn {r h} (k : γ ∈ (agreeWithOneOn r _
  h).subgroupOf _) v : S.ratToInf γ v ∈ (agreeWithOneOn r _ h).subgroupOf _ := by aesop

/-- For adelic x in the unipotent group 𝖴, left translation by the archimedean part of x
multiplies W(y) by ψ(−σ(x)/gϖ) divided by the finite character `Filling.unipotentChar` of the finite
part of x; σ is `simpleRootSum`. -/
lemma besselFn_adelicToInf_mul [Side] (h : x ∈ besselU) y : S.besselFn (S.adelicToInf x * y) =
    (stdAddChar E (↑(-(S.g * S.ϖ : E)⁻¹) * simpleRootSum x) / S.unipotentChar (S.adelicToFin x)) •
  S.besselFn y := by
  set z : 𝔸 E := _ * _; rw [show unipotentChar .. = ψf E z.2 by aesop]
  simp [besselFn, fun v ↦ (by simp [z, simpleRootSum, fst_sum, ← sum_mul, ↓adelicToInf_apply,
    ↓basisScale_besselFrame, pow_sub₀, pow_succ', div_eq_inv_mul, coe_kappa, field] : simpleRootSum
    (S.adelicToInf x v) = -π * 2 * .I * z.1 v), stdAddChar, wave, ↓sub_conj, ← Complex.exp_sum,
    mul_sum, sum_mul, ((besselSys ..).tail.isBesselFunction _).2 (S.adelicToInf x _)
    (conj_mem_unitriangular (blockTriangular_diagonal _) (h.map_mem_unitriangularOn _))]

lemma besselFn_ratToInf_mul [Side] (h : γ ∈ besselU) y : S.besselFn (S.ratToInf γ * y) =
  (S.unipotentChar (S.ratToFin γ))⁻¹ • S.besselFn y := (besselFn_adelicToInf_mul
  (h.map_mem_unitriangularOn _) y).trans (by simp [← map_mul, -map_neg, ratToFin])

end

variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) {F} [CommRing F]

attribute [local instance 0] starRingOfComm

lemma isUnimodular_latMiddle [StarRing F] {R} :
  IsUnimodular R (S.latMiddle F) := by simp [isUnimodular_latMiddleGram]

instance [StarRing F] : IsHermUnit (S.latMiddle F) :=
  S.isUnimodular_latMiddle (R := ⊤).rec (⟨·, ·.imp (by simp)⟩)

lemma transpose_splitGram : (S.latMiddle F).splitGramᵀ = (S.latMiddle F).splitGram :=
  .trans (by rfl) conjTranspose_eq

/-- The automorphism s ↦ J⁻¹s⁻ᵀJ of the general linear group over F if b is true, else the
identity; J is the Gram matrix in the lattice basis. -/
def idOrInvAdjoint b :=
  cond b (MulAut.conj (isUnit (J := (S.latMiddle F).splitGram)).unit⁻¹ * invTransposeGL) 1

/-- For a chosen place w above q₀ or q₁ and a Boolean, the ring homomorphism from the integral
finite adeles to the residue field at w: reduction modulo w, preceded by conjugation if the
Boolean is true. -/
def reduceAboveG (x : (Σ i, S.chosenPlaces i) × _) :=
  (reduceAt x.1.2.1).comp (cond x.2 starRingAut 1).toRingHom

/-- For k in K with reduction s at a chosen place w: the entrywise conjugate of k reduces modulo
w to J⁻¹s⁻ᵀJ (case b true); for b false both sides are s. -/
lemma intGL_map_reduceAboveG (k : S.latStabilizer) i w b : intGL.map (S.reduceAboveG (⟨i, w⟩, b))
  ⟨k, k.2⟩ = S.idOrInvAdjoint b (S.reduction k i w) := b.rec rfl (k.rec fun k ⟨g, e⟩ ↦ by
  obtain ⟨g, -, ⟨⟩⟩ :=
    U.mem_range_map (by simp) (Ô E).subtype_injective isUnit (S.map_splitGram_latMiddle _) congr($e)
  simpa [idOrInvAdjoint, mul_assoc, eq_inv_mul_iff_mul_eq, Units.ext_iff, map_splitGram_latMiddle,
    transpose_splitGram, -coe_units_inv]
    using! congr($(U.form_mul_inv_eq g)ᵀ.map (reduceAt w)).symm)

lemma gIdele_val : S.gIdele.1 = S.g := by simp [gIdele]

lemma gIdele_mem : ↑S.gIdele ∈ Ô E := by simp [gIdele, mul_mem]

lemma forall_selfDualChar_mul_eq_one_iff a : (∀ r : Ô E, S.selfDualChar (r * a) = 1) ↔ a ∈ Ô E := by
  simpa [selfDualChar, map_eq_one_iff coeHom @Circle.ext, ← Algebra.smul_def, ← mul_neg,
    forall_ψf_mul_eq_one, ← Algebra.mul_smul_comm, S.span_ϖ, Ideal.mem_span_singleton',
    -algebraMap_smul] using ⟨(one_mul a ▸ · 1), fun h _ ↦ mul_mem (coe_mem_Ô _) h⟩

lemma selfDualChar_eq_one_of_mem : ∀ x ∈ Ô E,
  S.selfDualChar x = 1 := by simpa using S.forall_selfDualChar_mul_eq_one_iff 1

lemma inv_gIdele_smul_mem_iff r : S.gIdele⁻¹ • r.1 ∈ Ô E ↔ ∀ x, S.reduceAboveG x
  r = 0 := by simpa [dvd_def, Subtype.ext_iff,
  ← gIdele_val, -Nat.cast_mul, reduceAboveG, ← S.gIdele.inv_mul_eq_iff_eq_mul] using! S.g_dvd_iff r

lemma principalLevel_eq_unitaryLevel : S.principalLevel = unitaryLevel (Ô E) S.gIdele _ :=
  le_antisymm (fun _ ⟨k, h, e⟩ ↦ e ▸ ⟨k.2, ((S.inv_gIdele_smul_mem_iff ⟨_, _⟩).2 fun _ ↦
  map_eq_one.1 ((intGL_map_reduceAboveG ..).trans (by aesop)) · ·)⟩) fun k ⟨m, h⟩ ↦ ⟨⟨k, m⟩,
  funext₂ (map_eq_one.2 fun _ _ ↦ (inv_gIdele_smul_mem_iff ..).1 (by apply h) ⟨⟨·, ·⟩, false⟩), rfl⟩
