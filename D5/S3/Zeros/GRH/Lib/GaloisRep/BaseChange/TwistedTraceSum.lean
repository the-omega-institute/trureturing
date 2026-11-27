/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/TwistedTraceSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/TwistedTraceSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.BaseChange.TwistedTraceSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/BaseChange/TwistedTraceSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.BaseChangePlaces
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.LocalTranslates
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Level decomposition and commuting families of local and spherical operators for the trace
comparison. Twisted trace of Hecke operator on definite unitary group as weighted orbital sum. -/

open Finset HasFiniteType DoubleCoset Gf LinearMap Set Subgroup

variable {E E' n W A} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E n) W} {S T : Set (FinPlace E)}
  (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) [Group A] (a : A →* Gf E n) (r : Gf E n →* A)

/-- The homomorphism a maps into the elements supported on S ∪ S̄, r∘a is the identity, and the
kernel of r consists of the elements trivial at S. -/
def IsLocalRetraction S := (∀ g, a g ∈ supportedOn n S) ∧ (∀ g, r (a g) = g) ∧ r.ker = trivialOn n S

section

attribute [local simp] supportedOn localLevel SetLike.ext_iff placesAbove funext_iff heckeFun_sum
  leftTranslation

/-- At a level L ≤ K_0 given by L₀ at S and B ∩ C elsewhere, commuting Hecke operators D_j at S
and the T_{u,i} at spherical split u off S ∪ S̄ preserve π^L and commute; suitable products
with D_k come from explicit functions (`IsOperatorOf`). -/
lemma exists_commuting_hecke_family L {L₀ B C} (hK : L ≤ Kf ..) {J X} {F : J → _} (hF : ∀ j,
  IsBiInvariant L₀ (F j)) {u : X → _} (hu : ∀ x, (u x).IsSplit) (hX : ∀ x, u x ∉ S.conjClosure ∧
  maxCompactAt n (u x) ≤ L) : let ρ := π.comp a
  let V :=
    levelSpace ρ L₀; let D j := heckeFun ρ L₀ (F j); let W := levelSpace π (trivialOn n S ⊓ L)
      let T := Sum.elim D fun x ↦ heckeSplit π (hu (Prod.fst x)) x.2; IsLocalRetraction a r S → L =
        .comap r L₀ ⊓ (B ⊓ C) → (∀ g, a g ∈ B ⊓ C) → (∀ i j, EqOn (D i * D j) (D j * D i) V) →
        levelSpace π L = V ⊓ W ∧ (∀ g, (∀ v ∈ W, ρ g v ∈ W) ∧ ∀ x, Commute (T (.inr x)) (ρ g)) ∧
        ∃ s : ∀ _, _, let A i := (T i).restrict (s i); (∀ i j, Commute (A i) (A j)) ∧ ∃ R : J → _ →
          _ → _, ∀ k, R k (A (.inl k)) (indicator B 1) ∧ ∀ {t φ},
      R k t φ → IsOperatorOf π L t (F k ∘ r * (φ * indicator C 1)) ∧ (∀ {i j},
          EqOn (D i * D k) (D j) V → R j (A (.inl i) * t) φ) ∧ ∀ x, supportedOn n {u x.1} ≤ C →
          R k (A (.inr x) * t) (heckeSplit leftTranslation (hu x.1) x.2 φ) := by
  rintro ρ V D W T ⟨p, q, o⟩ rfl hN c; simp at hN
  refine (fun E w ↦ ⟨E, w, Sum.rec (E ▸ fun j v h ↦ ⟨(hF j).heckeFun_mem h.1, by simp [T, D, hF,
    sum_mem, W.smul_mem, (w _).1 _ h.2]⟩) fun _ _ h ↦ heckeSplit_mem_levelSpace _ _ (levelSpace_anti
    (hX _).2 h) hK h, ?_⟩) ?_ fun g ↦
    ⟨fun _ h ↦ map_mem_levelSpace_of_commute h (commute_supportedOn_trivialOn (p g) ·.2.1
    |>.symm.map _), fun x ↦ LinearMap.ext (by simp_all [T, ρ, heckeSplit_comm_of_trivialOn])⟩
  simp +contextual +zetaDelta [iff_def, ← o, q, hN]; intro _ _ h k _ _ _
  simpa [*, mul_mem, -map_inv] using h (k * a (r k)⁻¹)
  intro Z; refine ⟨?m, fun k t φ ↦ ∃ T, t = Z _ * T ∧ ∀ i, IsOperatorOf π _ (Z (.inl i) * T)
    (F i ∘ r * (φ * _)), fun k ↦ ⟨⟨1, rfl, fun i ↦ .heckeFun_mul (hF i).1 ?_ ⟨1, rfl, by simp⟩⟩,
    @fun | _, _, ⟨T, rfl, h⟩ => ⟨h k, fun H ↦ ⟨T, by ext; exact H (E.le (by simp)).1, h⟩,
    fun x H ↦ ⟨_, (?m _ _).left_comm _, fun i ↦
    (?m _ _).left_comm _ ▸ (h i).heckeFun_mul (isBiInvariant_basicDoubleCoset _).1 (map_heckeSplit _
    _ (mulLeft ℂ (F i ∘ r) * mulRight ..) fun g e ↦ by simp [indicator_subgroup_mul_left, H e,
    r.mem_ker.1 (o ▸ supportedOn_compl.le (supportedOn_mono (by grind) e))])⟩⟩⟩⟩
  rintro ⟨⟩ ⟨⟩ <;> ext ⟨_, v⟩ <;> solve_by_elim [heckeSplit_comm, symm, (E.le v).1, map_heckeFun _
    (hF _).1 fun g ↦ congr($((w g).2 _) _), levelSpace_anti (hX _).2]
  choose _ _ using QuotientGroup.mk_out_eq_mul L₀
  simp [cosetFn, Finsupp.single_apply, QuotientGroup.eq, *, indicator, mul_mem_cancel_left, ite_and,
    ← @QuotientGroup.eq A]; lia

lemma isLocalRetraction_atSplit n [Fintype n] {w u} (h : ∀ v, .below E v = w ↔ v = u) hu hw :
    IsLocalRetraction (n := n) (atSplit hw) (atPlace w) {w} ∧ IsLocalRetraction (n :=
  n) (atSplit hu) (atPlace u) (placesAbove E' {w}) ∧ localLevel n (placesAbove _ {w}) =
  .comap (atPlace u) (intGL n Valued.v.integer) := by simp_all [IsLocalRetraction, ← below_star,
  star_eq_iff_star_eq, atPlace_star_eq_one_iff, atPlace_atSplit_of_ne]; tauto

lemma Gf.supportedOn_le_trivialOn (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) : supportedOn n S ≤
  trivialOn n T := biInf_mono H

lemma exists_remaining_places (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) {K} (h : ∀ x : T, ∀ u ∈ placesAbove
  _ {x.1}, K u = Kw ..) : ∃ Y, idem (placesAbove _ T) * idem (placesAbove E' Y) = 0 ∧
  supportedOn n (placesAbove _ T) ≤ localLevel n (placesAbove _ Y) K ∧
  placesAbove _ (T ∪ Y) = (placesAbove E' S)ᶜ ∧ idem (placesAbove _ T) + idem (placesAbove _ Y) =
  1 - idem (placesAbove E' S) ∧ localLevel n (placesAbove _ S)ᶜ K = localLevel n (placesAbove _ T) ⊓
  localLevel n (placesAbove E' Y) K := ⟨(S ∪ T).conjClosureᶜ, by
  simp_all [LE.le, Set.ext_iff, DFunLike.ext_iff, idem_apply, below_star]
  grind [star_star, one_mem]⟩

end

/-- Twisted trace formula on definite V: for compatible σ, τ, s and open σ-stable L ≤ K ≤ K_0,
some c ≠ 0 makes the trace on L-fixed forms of the Hecke operator of φ times ψ ↦ s∘ψ∘σ⁻¹ a
sample sum (`IsSampleTotal`) of weight c of φ(x⁻¹γσ(x)) tr(ρ(γ)s). -/
lemma Space.isSampleTotal_twisted_trace {E n} [Field E] [CMType E] [Fintype n] (V :
  Space E _ 1) κ {K L} (σ : _ ≃* _) (cσ : Continuous σ.symm) (hK : K ≤ Kf E n) (hL : L ≤ K) (oL :
  L.IsOpen) (hσ : L.comap σ = L) (τ : _ ≃* _) : let j := V.embFin; let ρ := V.weightRep _ κ.2; (∀ γ,
      j (τ γ) = σ (j γ)) → ∀ s, (∀ γ, s * ρ γ = ρ (τ γ) * s) → ∃ c ≠ 0, ∃ h h', ∀ {φ T},
      IsOperatorOf (V.formTranslation κ) L T φ → IsSampleTotal (fun p q : _ × _ ↦ {g | q.1⁻¹ * j g *
      p.1 ∈ K ∧ g⁻¹ * q.2 * τ g = p.2}) (fun y ↦ φ (y.1⁻¹ * j y.2 * σ y.1) * (ρ y.2 * s).trace ℂ _)
      c ((T * ((s.compLeft _ ∘ₗ funLeft ℂ _ σ.symm).restrict h).restrict h').trace ℂ _) := by
  intro j ρ hτ s hs
  have := V.hasFiniteType_of_isLevel.of_le hK (isOpen_mono hL oL)
  refine ⟨_, Nat.cast_ne_zero.2 (this.4.relIndex_ne_zero oL), fun _ h ↦ ⟨(comap σ.symm.toMonoidHom
    _).isOpen_mono (by aesop_cat) (cσ.1 _ h.1), (reindex_equiv τ).1.2 (by simp_all [j, ρ, forms,
    SmoothForm, DFunLike.ext_iff])⟩, fun _ h k ↦ ?_, fun ⟨a, e, C⟩ ↦ e.substr ?_⟩
  ext; simpa [LinearMap.restrict] using congr(s ($(h ⟨σ.symm k, hσ.le (by simp)⟩).1 _) _)
  have := this.of_le hL oL
  choose S hS cS using exists_transporter V.Γf Fact.out .rfl
  have N {J} [HasFiniteType V.Γf J] h x := classSum_eq_relIndex_smul (L := L) (f := fun y ↦ (#(S J x
    y) : ℂ)) h 1 (by simp; rfl) fun y ↦ (by rw [cS, cS, out_eq', mul_one] : _ = (#(S J x y) : ℂ))
  simp_rw [classSum, finsum_eq_sum_of_fintype, Rat.smul_def] at N
  conv at N in _ * ∑ _,
    _ => simp [cS, out_eq', ↓card_classAut_out x, -mem_classAut, -MonoidHom.coe_range]
  have f x : (fun γ ↦ cosetFn L a (x⁻¹ * j γ * σ x) * (ρ γ * s).trace ℂ _).HasFiniteSupport :=
    .mul_left ((cosetFn L a).hasFiniteSupport.preimage' fun q _ ↦ .ofFinset (S L (x * q.out) (σ x))
    (by simp [j, *, mul_assoc, ← QuotientGroup.eq, eq_comm])) _
  exact ⟨∑ i, ∑ γ ∈ _, .single (_, γ) _, (trace_eq_weighted_sum (·.out) _ (LinearMap.domRestrict
    (Submodule.subtype _) _) (le_antisymm (fun _ ⟨φ, e⟩ ↦ e ▸ ⟨⟨φ.1.2.2, by simp⟩, (congr($(φ.2
    ·).1))⟩) fun F h ↦ ⟨⟨⟨F, mem_smoothFunctions_of_eigen _ oL h.2, h.1.1⟩, (Subtype.ext <| h.2 ·)⟩,
    rfl⟩) σ _ (by simp [*, mul_assoc]) (D := ∅) ((ite_eq_left id).mpr <| N le_rfl · |>.trans
      (by simp))
    (fun _ ↦ by simpa [-map_mul, asAlgebraHom_eq_sum_support] using! congr($(C _).1)) hσ).2.trans
    (by simp [j, ρ, ← hτ, hs,
    (finsum_comp _ τ.bijective).trans (finsum_eq_sum _ (f _)), mul_sum, -MonoidHom.coe_range]; rfl),
    fun y h ↦ by simpa [*, mul_sum, ← ncard_coe_finset, ↓card_eq_sum_card_fiberwise fun g a ↦
    (f _).mem_toFinset.2 (h (_, g⁻¹ * y.2 * τ g) g ⟨((hS ..).1 a).2, rfl⟩)] using! N hL y.1⟩
