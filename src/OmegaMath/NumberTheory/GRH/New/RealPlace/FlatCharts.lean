import OmegaMath.NumberTheory.GRH.New.RealPlace.LevelGauge
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Tower method: pairings of kernels bounded floor by floor (see
New.RealPlace.LocalTheorem).

This file: Gauge estimates: flat charts, fibre masses, nearness, supports and weights on floors. -/

open Finset Sum HyperbolicBasis ENNReal Function Level Matrix MeasureTheory Place Set Size TraceOne
  MeasureTheory.Measure

attribute [local simp] mul_eq_top Fintype.card_subtype IsUnit.pow fromBlocks_mulVec mulVec_sub
  vecsOfSize Size.neg_star_mem_ofSize Size.zero_one_mem_ofSize inclMatrix ite_mem mul_assoc mul_sub
  smul_sub sub_mul

variable {A ι} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [Place A]
  [Fintype ι] {C K M m i j p q} {a : Fin 𝔰.ϱ} {T : 𝔰.Form A} [IsHermUnit T.splitGram] {F :
  Level ι T m} {Γ : Gauge F} {b : Fin 𝔰.n} {g x y σ ξ : T.G} (h : ξ ∈ unitriGroup j)

/-- Let u be a unit, v in V_{a+1}. If the column e*_{a+1} of (ν·ν(v,β) − 1)/u has size i for
some ν in 𝒩_{<a}, then v/u and (β − τh(v,v))/u have size i. -/
lemma Size.mem_vecsOfSize_of_heisenbergElem {S : Size T} {u :
  Aˣ} {t} : let v := inclMatrix A (↑) *ᵥ t.1; (∃ ν ∈ T.unipotentBelow a, u⁻¹.1 • (((ν *
    heisenbergElem a t).1.1 - 1) · (eStar a)) ∈ S.vecsOfSize i) → u⁻¹.1 • v ∈ S.vecsOfSize i ∧
    u⁻¹ * (t.2 - τ * star v ⬝ᵥ T.splitGram *ᵥ v) ∈ S.ofSize i := fun ⟨ν, hν, h⟩ ↦ by
  have E n k l := congr(_ * ($(unipotentBelow_mulVec_apply hν n k l) - _) ∈ _).mp (h k)
  simp [heisenbergElem, eichlerMap, vecMulVec, inclMatrix_val_mulVec, -inclMatrix] at *; grind

@[simp] lemma Level.isNear_mul_iff (h : ξ ∈ unitriGroup j) : F.IsNear j (ξ * g) ↔ F.IsNear j g :=
    (Equiv.mulRight ξ).exists_congr (by simp_all [mul_mem_cancel_right])

lemma Level.IsNear.of_floorGroup_mul (h : F.IsNear i (x * g)) (hx : x ∈ GT j) (ha : j ≤
  i := by first | rfl | lia) :
  F.IsNear j g := (isNear_mul_iff (mem_unitriGroup_of_mem_floorGroup hx)).1 (by grind [IsNear])

lemma Level.measurableSet_isNear : MeasurableSet {g | F.IsNear j g} := ((isClosed_of_entries_eq_one
  (S := unitriGroup j) .rfl).mul_right_of_isCompact F.box_spec.1).measurableSet.congr
  (ext fun _ ↦ inv_surjective.exists.trans (by simp [IsNear, inv_mul_eq_iff_eq_mul]))

/-- If every floor a ≤ ϱ has mass at most V, then for any l and c the measure θ_{ϱ+1} ∗ ⋯ ∗ θ_l
gives the σ with σc in 𝖴·(box) mass at most V^{ϱ+1−l}. -/
lemma Level.upperMeasure_isNear_le {V} (hV : ∀ a : Fin 𝔰.n, F.FloorMassLe a V 1) l c :
    F.upperMeasure l {g | F.IsNear (𝔰.ϱ + 2) (g * c)} ≤ V ^ (𝔰.n - l) := by
  induction' e : _ - l with i ih generalizing l c
  cases (by lia : l = 𝔰.n ∨ 𝔰.ϱ + 2 - l = 0) <;>
    simp [*, descConv, IsNear, measureH_spec, indicator_apply_le', -Subtype.exists]
  erw [upperMeasure_eq_succ_mconv,
    mconv_apply_eq_lintegral (measurable_mul_const c measurableSet_isNear)]
  simp [-upperMeasure, FloorMassLe] at *
  grw [← setLIntegral_eq_of_support_subset, ih, setLIntegral_const, hV ⟨l, by lia⟩ _ c.2, pow_succ]
  exacts [by lia, support_subset_iff'.2 fun _ _ ↦
    mono_null (by grind [IsNear.of_floorGroup_mul]) (ae_descConv_mem ae_floorMeasure_mem)]

lemma Level.isOpen_floorValues : IsOpen {((x, y), c) : _ × A | c ∈ F.floorValues a x y} :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨w, _⟩ ↦ ⟨ofPred _, fun _ ↦ (⟨_, ⟨·, by grind⟩,
  update_self _ _ w⟩), by apply_rules [IsOpen.and, F.ball_spec.1.preimage] <;> fun_prop, by aesop⟩

lemma Level.floorValues_mul (h : ξ ∈ unitriGroup (a + 1)) : F.floorValues a (ξ * x) y =
  F.floorValues a x y := by
  ext
  use .imp' (mulVec ξ⁻¹) ?_, .imp' (mulVec ξ) ?_ <;> simp <;>
    grind [unitriGroup_mulVec_dual, inv_mem h, coe_units_inv, Subgroup.coe_inv]

@[simp] lemma Level.volume_floorValues_ne_zero_ne_top : volume (F.floorValues a x y) ≠ 0 ∧
  volume (F.floorValues a x y) ≠ ∞ := ⟨(isOpen_floorValues.preimage (.prodMk_right (x,
  y))).measure_ne_zero _ ⟨0, 0, by simp [ball_spec]⟩, (((F.ball_spec.2.2.preimage_smul x⁻¹).image
  (by fun_prop)).measure_ne_top <| measure_mono_top (image_mono fun _ ↦ (subset_closure ·.1.1)) ·)⟩

lemma Level.floorWeight_succ : F.floorWeight (a + 1) x y =
  F.floorWeight a x y * volume (F.floorValues a x y) ^ F.volumeExponent := by
  simp [floorWeight, filter_gt_eq_Iio, prod_Iio_mul_eq_prod_Iic, filter_ge_eq_Iic]

@[simp] lemma Level.floorWeight_ne_zero_and_ne_top : F.floorWeight j x y ≠ 0 ∧
  F.floorWeight j x y ≠ ∞ := by simp [floorWeight, prod_ne_top, prod_eq_zero_iff]

include h in
@[simp] lemma Level.floorWeight_mul_left : F.floorWeight j (ξ * x) y = F.floorWeight j x y :=
  prod_congr rfl (by grind [floorValues_mul])

include h in
@[simp] lemma Level.invWeight_mul : F.invWeight j x (ξ * g) =
  F.invWeight j x g := by simp [invWeight, indicator, h]

seal Finset.univ Finset.sum Finset.prod in
@[fun_prop] lemma measurable_floorWeight : Measurable ↿(F.floorWeight j) := measurable_prod _ fun _
  _ ↦ (measurable_measure_prodMk_left isOpen_floorValues.measurableSet).pow_const _

@[fun_prop] lemma Level.measurable_invWeight : Measurable (F.invWeight j x) :=
  .indicator (by fun_prop) measurableSet_isNear

namespace Gauge

lemma measurableSet_vecsOfSize {n} [Fintype n] :
  MeasurableSet (Γ.vecsOfSize (n := n) j) := .univ_pi' fun _ ↦ (Γ.isCompact_ofSize j).measurableSet

lemma mem_vecsOfSize_of_floorBasis_mulVec {x} (h : F.floorBasis b *ᵥ x ∈ Γ.vecsOfSize j) :
  x ∈ Γ.vecsOfSize (j + 4) := by
  have := ((by simp [HasMatSize, floorBasis, mul_apply, -ite_mul, sum_boole_mul, -star_sum,
    Γ.data_mem_ofSize.2.1 _] : Γ.HasMatSize 1 (F.floorBasis b)ᴴ).mul Γ.gram_mem_ofSize.1).mulVec h
  simp_all +arith [gram_floorBasis, dotProduct]

/-- In the basis of V_b, q is a product measure in (fixed, orthonormal, fibre) coordinates,
whose fibres give points of size j+4 mass at most μ(fixed coordinates), with ∫μ ≤ M. -/
def HasFibreBound (Γ : Gauge F) b q j M := ∃ (Z : Type) (_ : MeasurableSpace Z)
  (ζ : Measure Z), ∃ ρ k μ, SFinite ζ ∧ MeasurePreserving k ((volume.prod volume).prod ζ) ρ ∧ ρ.map
  (F.floorBasis b *ᵥ ·) = q ∧ (∀ r, r.1 = ((k r (inl 1), k r ∘ inr ∘ inl), k r ∘ inr ∘ inr ∘ inl))
  ∧ Measurable μ ∧ (∀ p w, ζ {z | k ((p, w), z) ∈ Γ.vecsOfSize (j + 4)} ≤ μ p) ∧ ∫⁻ p, μ p ≤ M

lemma setLIntegral_le_of_hasFibreBound {Φ G : _ → _} : Γ.HasFibreBound b q j M →
  (∀ p, Measurable (G p) ∧ ∫⁻ w, G p w ≤ K) → (∀ x ∈ Γ.vecsOfSize (j + 4), Φ (F.floorBasis b *ᵥ x) ≤
  G (x (inl 1), x ∘ inr ∘ inl) (x ∘ inr ∘ inr ∘ inl)) → ∫⁻ x in Γ.vecsOfSize j, Φ x ∂q ≤ M * K := by
  rintro ⟨Z, _, ζ, _, k, μ, _, ⟨_, rfl⟩, rfl, _, _, hμ, hM⟩ hG _
  grw [← lintegral_indicator, lintegral_map_le _ (by fun_prop),
    lintegral_map_le _ (by fun_prop), ← hM, lintegral_prod_le,
    lintegral_prod_le, ← lintegral_mul_const]
  gcongr
  grw [mul_comm, ← (hG ‹_›).2, ← lintegral_mul_const, ← hμ _ ‹_›, ← lintegral_indicator_const_le]
  gcongr; repeat grind [indicator, mem_vecsOfSize_of_floorBasis_mulVec, zero_le,
    measurableSet_vecsOfSize]

/-- If the cone measure δ₀ on the hyperbolic planes of the chart of V_b gives the vectors of
size j+5 mass at most M, then the quadric measure δ^(b) satisfies the fibre bound
`Gauge.HasFibreBound` at size j with constant M. -/
lemma hasFibreBound_floorQuadric_of_le (e : quadricMeasure (hyperbolicGram (FloorPairs b m) (0 :
  Matrix Empty ..)) 0 (Γ.vecsOfSize (j + 5)) ≤ M) : Γ.HasFibreBound b (F.floorQuadric b) j M :=
  have N := MeasurePreserving.comp ⟨by fun_prop, rfl⟩ (measurePreserving_shuffle_coords.comp (.prod
    ⟨measurable_prodMk_right, by rw [volume_pi_eq_dirac, prod_dirac]⟩ (.id _)))
  ⟨_, _, _, _, _, _, inferInstance, .comp ⟨by fun_prop, rfl⟩ measurePreserving_shuffle_coords,
    rfl, by tauto, measurable_measure_prodMk_left (N.1 measurableSet_vecsOfSize), fun p w ↦
    measure_le_of_sub_mem fun y k ↦ ⟨y, fun z h ↦ by simp [flatChart, star_sumElim] at *; grind
    [mem_ofSize_mono, Size.sub_mem_ofSize, sub_mem_ofSize h.1.1 k.1.1]⟩, ((N.measure_preimage_le
    _).trans e).trans_eq' (Measure.prod_apply (N.1 measurableSet_vecsOfSize))⟩

/-- In a gauge, the quadric measure δ^(b) on V_b satisfies the fibre bound `Gauge.HasFibreBound`
at size j with constant Λ^{99(ϱ+1)(j+6)}. -/
lemma hasFibreBound_floorQuadric : Γ.HasFibreBound b (F.floorQuadric b) j (Γ.Λ ^ (99 * 𝔰.n *
  (j + 6))) := hasFibreBound_floorQuadric_of_le (by apply fib <;> simp [card_finset_fin_le])

/-- For a gauge with constant Λ, every b ≤ ϱ and every j, the volume measure of V_b satisfies
the fibre bound `Gauge.HasFibreBound` for coordinates of size j+4, with total bound
Λ^(99n(j+6)), n = ϱ + 1. -/
lemma hasFibreBound_floorVolume : Γ.HasFibreBound b (floorVolume b) j (Γ.Λ ^ (99 * 𝔰.n *
  (j + 6))) := have K := ((Γ.isCompact_ofSize _).measurableSet.prod measurableSet_vecsOfSize).prod
                 (measurableSet_vecsOfSize.prod (Γ.isCompact_ofSize _).measurableSet)
  ⟨_, _, _, _, _, _, inferInstance, measurePreserving_pair_sumElim.comp
    (measurePreserving_swap.comp measurePreserving_shuffle_coords), map_floorBasis_volume ..,
    by tauto, measurable_measure_prodMk_left K, fun p w ↦ measure_mono fun _ ↦ by simp; tauto, by
    simp [↓← Measure.prod_apply K, volume, ← mem_univ_pi, -Set.mem_pi]
    grw [volume_le, card_finset_fin_le, Γ.two_le_and_pairs_le.2] <;> ring_nf <;> bound⟩

/-- For a unit u and measurable Ψ, suppose Φ(ν(v,β)) ≠ 0, v ∈ V_{a+1}, forces Φ(ν(v,β)) ≤ Ψ(v/u)
and column e*_{a+1} of (ν'ν(v,β)⁻¹−1)/u of size j for some ν' ∈ 𝒩_{<a}. Then ∫Φ dη_a ≤
fl_a(u)Λ^{j+2}∫_{size j}Ψ dv. -/
lemma lintegral_heisenbergMeasure_le {Φ Ψ : _ → _} (u : Aˣ) (k : ∫⁻ x in Γ.vecsOfSize j,
  Ψ x ∂floorVolume a.succ ≤ M) (h : ∀ t, let n := heisenbergElem a t; Φ n ≠ 0 →
    (∃ ν ∈ T.unipotentBelow a, u⁻¹.1 • (((ν * n⁻¹).1.1 - 1) · (eStar a)) ∈ Γ.vecsOfSize j) ∧
  Φ n ≤ C * Ψ (u⁻¹.1 • inclMatrix A (·.1) *ᵥ t.1)) (e : F.floorModulus a u * (Γ.Λ ^ (j + 2) * M) ≤
  K := by simp [floorModulus]; ring_nf; gcongr <;> simp) (m : Measurable Ψ := by fun_prop) : ∫⁻ n,
  Φ n ∂heisenbergMeasure a ≤ C * K := by
  grw [← e, mul_rotate', mul_rotate, floorModulus, mul_mul_mul_comm, mul_assoc, heisenbergMeasure,
    dite_eq_left, ← k, ← lintegral_mul_const, setLIntegral_map, ← lintegral_indicator_le,
    lintegral_map_le, ← lintegral_mul_const', lintegral_prod_le,
    lintegral_eq_mul_lintegral_map (map_mulVec_volume _ (u.1 • 1) _), lintegral_map_le]
  gcongr; simp [↓card_succ_le_floorOf]
  choose V E using fun {t} n ↦
    mem_vecsOfSize_of_heisenbergElem (heisenbergElem_inv (T := T) ▸ (h t n).1)
  grw [← setLIntegral_eq_of_support_subset .rfl, setLIntegral_mono _ fun t n ↦ ?_,
    setLIntegral_const, skewMeasure_le_of_sub_mem u⁻¹ fun z h y k ↦ Eq.subst (by simp; ring)
    (sub_mem_ofSize (Γ.mul_mem_ofSize Γ.data_mem_ofSize.2.2 (sub_mem_ofSize (E k.1) (E h.1)))
    (mem_ofSize_mono (sub_mem_ofSize (E h.2) (E k.2))))]
  any_goals grw [(h _ n).2, mul_comm, indicator_of_mem (by simpa [mulVec_neg] using V n)]
  repeat' first | fun_prop | simp [one_le_c_and_ne_top, ↓measurableSet_vecsOfSize, smul_smul,
    mul_pow, ← pow_mul, ← rpow_mul_natCast]
  grw [volume_le]; bound

lemma setLIntegral_orthonormalPart_le {φ} (h : Γ.HasFibreBound b q j M) (k : ∫⁻ w in Γ.vecsOfSize
  (j + 4), φ w ≤ K) (m : Measurable φ := by fun_prop) : ∫⁻ x in Γ.vecsOfSize j,
  φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ x) ∂q ≤ M * K := setLIntegral_le_of_hasFibreBound h
  (fun _ ↦ ⟨m.indicator measurableSet_vecsOfSize, by grw [lintegral_indicator_le, k]⟩) fun x e ↦ by
  simpa [← mulVec_mulVec, comp_def, e _, show F.orthonormalPart =
    (F.floorBasis b).toCols₂.toCols₂.toCols₁ by simp [entrywise, floorBasis]] using! congr(φ
    (($(gram_floorBasis ..) *ᵥ x) ∘ inr ∘ inr ∘ inl)).le

lemma measurableSet_positionsOfSize : MeasurableSet Γ.positionsOfSize :=
  F.box_spec.2.inter ((Γ.isCompact_ofSize 1).matrix.measurableSet.preimage (by fun_prop))

/-- Let g lie in the box, and let x, y be positions with (x−1)/𝑔 and (y−1)/𝑔 of size 1, 𝑔 the
unit of the level. Then (gx(gy)⁻¹ − 1)/𝑔 has size 14. -/
lemma conj_mul_inv_close_to_one (hg : g ∈ F.boxSet) (h : x ∈ Γ.positionsOfSize) (k :
  y ∈ Γ.positionsOfSize) (e : σ = g * x * (g * y)⁻¹) : Γ.HasMatSize 14 (F.g⁻¹.1 • (σ.1.1 - 1)) := by
  simpa [e] using ((Γ.hasMatSize_box hg).mul (h.2.sub k.2)).mul (((Γ.hasMatSize_box hg).mul fun a
    b ↦ by simpa using sub_mem_ofSize (Γ.mul_mem_ofSize Γ.data_mem_ofSize.1
    (k.2 a b)) (Γ.neg_star_mem_ofSize.1.2 (HasMatSize.one a b))).inv (x := g * y))

/-- In a gauge, let b ≤ ϱ, σ lie in H_b and g have entries of size i. If σg is near at b+1, then
the vector σ⁻¹f_{b+1} has size i+6. -/
lemma orbitPoint_mem_vecsOfSize (hσ : σ ∈ GT b) (hg : Γ.HasMatSize i g.1.1) :
    F.IsNear (b + 1) (σ * g) → orbitPoint b σ ∈ Γ.vecsOfSize (i + 6) := fun ⟨ξ, a, c⟩ k ↦ by
  simpa [orbitPoint, by simpa using floorGroup_apply_besselFrame (inv_mem hσ) (inv_mem a) k] using
    fun _ ↦ hg.mul (Γ.hasMatSize_box c).inv ..

/-- In a gauge, let p be a head of length j ≤ ϱ. If g and w_p⁻¹g are near at j, some σ in H_j
makes σg of size 60(ϱ+1)² and σw_p⁻¹g of size 99(ϱ+1)². -/
lemma exists_hasMatSize_of_isNear (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p) : F.IsNear j g →
  F.IsNear j ((weylElem j p)⁻¹ * g) → ∃ σ ∈ GT j, Γ.HasMatSize (60 * 𝔰.n ^ 2) (σ * g).1.1 ∧
  Γ.HasMatSize (99 * 𝔰.n ^ 2) (σ * ((weylElem j p)⁻¹ * g)).1.1 :=
  fun ⟨_, a, c⟩ h ↦ (exists_floorGroup_mul_unipotentBelow a).imp fun σ ⟨b, ν, n, _⟩ ↦
  ⟨b, ((weylElem_mul_left_comm b).2 ▸ (hasMatSize_of_isHead Γ.hasMatSize_box
  hj · ⟨unipotentBelow_le_unitriGroup (conj_mem_unipotentBelow b n), by aesop⟩ hp
  (conj_mem_unipotentBelow b n))) ((isNear_mul_iff (mem_unitriGroup_of_mem_floorGroup b)).2 h)⟩

/-- Let p, q be heads of length j for a gauge S, with c/g of Γ-size 1 for c of S-size 10(ϱ+1) if
j ≠ 0. If ux, vy lie in the box (u, v ∈ 𝖴), (vy−ux)/g has Γ-size 2, w_p⁻¹x, w_q⁻¹y are near
at j, and each 𝔤_a(x,y), a > j, holds a unit with inverse of Γ-size 1, then (x⁻¹y−1)/g has
Γ-size 99(ϱ+1). -/
lemma hasMatSize_sub_one_of_floorValues {q} (S : Gauge F) (hj : j ≤ 𝔰.ϱ) (hp : S.IsHead j p) (hq :
  S.IsHead j q) (hS : j ≠ 0 → ∀ c ∈ S.ofSize (10 * 𝔰.n), F.g⁻¹ * c ∈ Γ.ofSize 1) : (∃ u ∈ T.besselU,
  ∃ v ∈ T.besselU, u * x ∈ F.boxSet ∧ v * (x * y) ∈ F.boxSet ∧ Γ.HasMatSize 2 (F.g⁻¹.1 • ((v *
  (x * y)).1.1 - (u * x).1.1))) → F.IsNear j ((weylElem j p)⁻¹ * x) → F.IsNear j ((weylElem j q)⁻¹ *
  (x * y)) → (∀ a, j ≤ a.1 → ∃ c : Aˣ, ↑c ∈ F.floorValues a x y ∧ ↑c⁻¹ ∈ Γ.ofSize 1) → Γ.HasMatSize
  (99 * 𝔰.n) (F.g⁻¹.1 • (y.1.1 - 1)) := fun ⟨u, hu, v, hv, k, n, d⟩ l o hc ↦ .mono
  (by simpa using (Γ.hasMatSize_box k).inv.mul (d.mono.sub (.mul (hasMatSize_one_sub_inv (c := 6)
  ((unipotentBelow_eq_besselU .refl).ge (mul_mem hv (inv_mem hu))) ⟨F.star_g, Γ.data_mem_ofSize.1⟩
  fun a _ ↦ if e : a < j then have z := (hS e.ne_bot _ <| (head_entries_mem_ofSize S.hasMatSize_box
    hj l ⟨mem_unitriGroup_of_mem_besselU hu, k⟩ hp e).2.2 ·)
  ⟨u.1.1 *ᵥ Pi.single (eStar a) 1, by grind [unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_besselU
    hu)], (mem_ofSize_mono <| by simpa using Γ.mul_mem_ofSize Γ.data_mem_ofSize.1 <| z ·),
    fun i ↦ by simpa [↓mulVec_mulVec] using mem_ofSize_mono (sub_mem_ofSize (z i) (hS e.ne_bot _
    ((head_entries_mem_ofSize S.hasMatSize_box hj o ⟨mem_unitriGroup_of_mem_besselU hv, n⟩ hq e).2.2
    i)))⟩ else (hc a (by lia)).elim fun c ⟨⟨w, ⟨⟨m, r⟩, z⟩, e⟩, h⟩ ↦ ⟨c⁻¹.1 • u *ᵥ w, by simp; grind
  [c.inv_mul, unitriGroup_mulVec_dual (mem_unitriGroup_of_mem_besselU hu)], (mem_ofSize_mono <| by
  simpa using Γ.mul_mem_ofSize h <| (Γ.hasMatSize_box k).mulVec (Γ.hasVecSize_ball m) ·),
  fun i ↦ by simpa using (Γ.mul_mem_ofSize h (sub_mem_ofSize (mem_ofSize_mono ((Γ.hasMatSize_box
  n).mulVec (Γ.hasVecSize_ball r) i)) (d.mulVec (Γ.hasVecSize_ball m) i)))⟩) (Γ.hasMatSize_box n))))
