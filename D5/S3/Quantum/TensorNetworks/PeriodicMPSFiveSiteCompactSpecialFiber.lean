/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactSpecialFiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactSpecialFiber
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart]
   utility: none
   digest: The special compact fiber consists of four ordinary points. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart

/-! Polynomial relations on the ordinary graph exclude limiting pencil
directions over the two exceptional base points. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSpecialFiber

open Set Filter PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCompactChart
  PeriodicMPSFiveSiteCompactIncidence PeriodicMPSProjectiveCoordinates
  PeriodicMPSFiveSiteTraceChart PeriodicMPSFiveSiteCoordinates
  PeriodicMPSFiveSiteAlignedFiber PeriodicMPSFiveSiteNormalization PeriodicMPSFiveSiteSpecialFiber
open scoped Topology ComplexConjugate

open private traceRatio continuousAt_traceRatio pencilRatio mixedRatio ambientDomain
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart
open private traceDirection pencil traceDirection_ne_zero pencil_ne_zero
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource
open private a b root from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteAlignedFiber
open private specialRay specialRay_gram
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialFiber

noncomputable section

private theorem projector_column {ι : Type*} [Fintype ι] (v : ι → ℂ) (j : ι) :
    (fun i => projector v i j) = (↑((PeriodicMPSProjectiveCoordinates.mass v)⁻¹) *
      conj (v j) : ℂ) • v := by
  funext i
  simp only [projector, outer, Matrix.smul_apply, Complex.real_smul, Pi.smul_apply, smul_eq_mul]
  ring

private def alignedPencil (p : Ambient) (j : Fin 6) : Fin 4 → ℂ :=
  let s := traceRatio p
  let v := fun i => p.1.2 i j
  let z := v 4 - 2 * s * v 3
  ![3 * v 3 - v 0, 2 * v 3 - v 0, z, v 5 - s * z - s ^ 2 * v 3]

private def alignedColumn (p : Ambient) : Fin 8 → ℂ :=
  shear (-traceRatio p) (fun i => p.2 i 3)

private def quadrics (v : Fin 4 → ℂ) : Fin 8 → ℂ :=
  aligned (v 0) (v 1) (v 2) (v 3)

private def relation (v : Fin 4 → ℂ) (f : Fin 8 → ℂ) : ℂ :=
  v 0 * v 1 * f 3 - v 0 * v 2 * f 1 - v 1 * (v 1 - v 0) * f 2

set_option maxHeartbeats 900000 in
-- Expanding the eight fixed-degree quadrics uses repeated polynomial normalization.
private theorem ordinary_relations (u : Inputs) (ht : (ordinary u).1.1 0 0 ≠ 0)
    (j : Fin 6) (i : Fin 8) :
    let v := alignedPencil (ordinary u) j
    let f := alignedColumn (ordinary u)
    quadrics v i * f 3 = quadrics v 3 * f i ∧ relation v f = 0 := by
  let t := u.val 0
  let s := u.val 1 / t
  let d := u.val 2
  let m := t * u.val 1 - u.val 4
  let z := m - 2 * s * d
  let w := u.val 3 - s * z - s ^ 2 * d
  let p := coordinates (u.val 0) (u.val 1) d (u.val 3) (u.val 4)
  let g := fun {ι : Type} [Fintype ι] (v : ι → ℂ) (k : ι) =>
    (↑((PeriodicMPSProjectiveCoordinates.mass v)⁻¹) : ℂ) * conj (v k)
  have htn : t ≠ 0 := (projector_diag_ne_zero_iff (traceDirection u.val) 0).mp ht
  have htr : traceRatio (ordinary u) = s :=
    projector_ratio (traceDirection u.val) 1 0 htn
  have hs : t * s = u.val 1 := mul_div_cancel₀ _ htn
  have hv : alignedPencil (ordinary u) j = g (pencil u.val) j •
      ![3 * d - t ^ 2, 2 * d - t ^ 2, z, w] := by
    unfold alignedPencil
    rw [htr]
    have hc := projector_column (pencil u.val) j
    change (fun i => (ordinary u).1.2 i j) = _ at hc
    have hentry (k : Fin 6) : (ordinary u).1.2 k j = (g (pencil u.val) j) * pencil u.val k :=
      congrFun hc k
    simp only [hentry]
    funext k
    fin_cases k <;>
      simp [pencil, d, m, t, z, w, Pi.smul_apply, smul_eq_mul, pow_two] <;> ring
  have hp : p = t • chart s (3 * d - t ^ 2) (2 * d - t ^ 2) z w := by
    have h := frame_trace_coordinates t 1 s d m (u.val 3)
    have he : t ^ 2 * s - m = u.val 4 := by
      dsimp only [m]
      rw [pow_two, mul_assoc, hs]
      ring
    have hm : z + 2 * s * d = m := by dsimp only [z]; ring
    have hw : w + s * z + s ^ 2 * d = u.val 3 := by dsimp only [w]; ring
    simp only [mul_one, hs, he] at h
    have hf := frame_first_chart s (t ^ 2) d z w
    rw [hm, hw] at hf
    rw [hf] at h
    exact h
  have hf : alignedColumn (ordinary u) =
      (g p 3 * t) • aligned (3 * d - t ^ 2) (2 * d - t ^ 2) z w := by
    unfold alignedColumn
    rw [htr]
    change shear (-s) (fun i => projector p i 3) = _
    rw [projector_column, shear_smul, show shear (-s) p =
      t • aligned (3 * d - t ^ 2) (2 * d - t ^ 2) z w by
        rw [hp, shear_smul, chart, shear_add, neg_add_cancel, shear_zero], smul_smul]
  dsimp only
  rw [hv, hf]
  constructor
  · fin_cases i <;> simp [quadrics, aligned, Pi.smul_apply, smul_eq_mul] <;> ring
  · simp [relation, aligned, Pi.smul_apply, smul_eq_mul]
    ring

private theorem alignedPencil_continuous {p : Ambient} (ht : p.1.1 0 0 ≠ 0) (j : Fin 6) :
    ContinuousAt (fun q => alignedPencil q j) p := by
  have ht' := continuousAt_traceRatio ht
  apply continuousAt_pi.mpr
  intro k
  fin_cases k <;> simp [alignedPencil] <;> fun_prop

private theorem alignedColumn_continuous {p : Ambient} (ht : p.1.1 0 0 ≠ 0) :
    ContinuousAt alignedColumn p := by
  have ht' := continuousAt_traceRatio ht
  apply continuousAt_pi.mpr
  intro k
  fin_cases k <;> simp [alignedColumn, shear] <;> fun_prop

private theorem compact_relations {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 ≠ 0)
    (j : Fin 6) (i : Fin 8) :
    let v := alignedPencil p j
    let f := alignedColumn p
    quadrics v i * f 3 = quadrics v 3 * f i ∧ relation v f = 0 := by
  let F : Ambient → ℂ × ℂ := fun q =>
    (quadrics (alignedPencil q j) i * alignedColumn q 3 -
      quadrics (alignedPencil q j) 3 * alignedColumn q i,
      relation (alignedPencil q j) (alignedColumn q))
  have hv := alignedPencil_continuous ht j
  have hf := alignedColumn_continuous ht
  have hv' (k : Fin 4) : ContinuousAt (fun q => alignedPencil q j k) p :=
    continuousAt_pi.mp hv k
  have hf' (k : Fin 8) : ContinuousAt (fun q => alignedColumn q k) p :=
    continuousAt_pi.mp hf k
  have hq (k : Fin 8) : ContinuousAt (fun q => quadrics (alignedPencil q j) k) p := by
    fin_cases k <;> simp [quadrics, aligned] <;> fun_prop
  have hF : ContinuousAt F p := by
    dsimp only [F, relation]
    fun_prop
  haveI : NeBot (𝓝[range ordinary] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have ht' : ∀ᶠ q in 𝓝[range ordinary] p, q.1.1 0 0 ≠ 0 :=
    nhdsWithin_le_nhds ((show ContinuousAt (fun q : Ambient => q.1.1 0 0) p by fun_prop)
      (isOpen_ne.mem_nhds ht))
  have he : F =ᶠ[𝓝[range ordinary] p] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin, ht'] with q hq hqt
    obtain ⟨u, rfl⟩ := hq
    obtain ⟨h₁, h₂⟩ := ordinary_relations u hqt j i
    exact Prod.ext (sub_eq_zero.mpr h₁) h₂
  have hzero := tendsto_nhds_unique hF.continuousWithinAt (tendsto_const_nhds.congr' he.symm)
  exact ⟨sub_eq_zero.mp (congrArg Prod.fst hzero), congrArg Prod.snd hzero⟩

private theorem pencil_incidence {p : Ambient} (hp : p ∈ source) (j : Fin 6)
    (i k : Fin 6)
    (h : ∀ v : Fin 5 → ℂ, v 0 * pencil v i = v 1 * pencil v k) :
    p.1.1 0 0 * p.1.2 i j = p.1.1 1 0 * p.1.2 k j := by
  apply closure_minimal (t := {q | q.1.1 0 0 * q.1.2 i j = q.1.1 1 0 * q.1.2 k j})
    _ (isClosed_eq (by fun_prop) (by fun_prop)) hp
  rintro _ ⟨u, rfl⟩
  have h₁ := congrFun (projector_column (traceDirection u.val) 0) (0 : Fin 2)
  have h₂ := congrFun (projector_column (traceDirection u.val) 0) (1 : Fin 2)
  have h₃ := congrFun (projector_column (pencil u.val) j) i
  have h₄ := congrFun (projector_column (pencil u.val) j) k
  change projector (traceDirection u.val) 0 0 * projector (pencil u.val) i j =
    projector (traceDirection u.val) 1 0 * projector (pencil u.val) k j
  rw [h₁, h₂, h₃, h₄]
  have h0 : traceDirection u.val 0 = u.val 0 := rfl
  have h1 : traceDirection u.val 1 = u.val 1 := rfl
  simp only [Pi.smul_apply, smul_eq_mul, h0, h1, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination
    (↑((PeriodicMPSProjectiveCoordinates.mass (traceDirection u.val))⁻¹) *
      conj (u.val 0) *
      (↑((PeriodicMPSProjectiveCoordinates.mass (pencil u.val))⁻¹) * conj (pencil u.val j))) * h u.val

private theorem exists_rep {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ}
    (h : P ∈ projective) : ∃ v : ι → ℂ, v ≠ 0 ∧ P = projector v := by
  obtain ⟨v, hv, rfl⟩ := h
  change PeriodicMPSProjectiveCoordinates.mass v = 1 at hv
  refine ⟨v, fun e => ?_, ?_⟩
  · simp [e, PeriodicMPSProjectiveCoordinates.mass] at hv
  · simp [projector, hv]

private theorem ray_ne_zero (s : ℂ) : ray s ≠ 0 := by
  intro e
  have h := congrFun e (3 : Fin 8)
  norm_num [ray] at h

/-- A lift of either special ray has the ordinary trace direction and one of
the two roots of the aligned pencil equation. -/
theorem lift_of_ray {p : Ambient} (hp : p ∈ source) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (hr : p.2 = projector (ray s)) :
    p = affine (root s) (b s) 0 0 ∨ p = affine (3 * b s - root s) (b s) 0 0 := by
  obtain ⟨t, ht, hT⟩ := exists_rep (source_subset_projective hp).1.1
  have ht₁ : t 1 = 0 := by
    by_contra hn
    exact (projector_diag_ne_zero_iff t 1).2 hn (hT ▸
      special_ray_trace_row_zero hp s hr 1)
  have ht₀ : t 0 ≠ 0 := by
    intro h
    exact ht (funext fun i => by fin_cases i <;> assumption)
  have hT₀ : p.1.1 0 0 ≠ 0 := hT.symm ▸ (projector_diag_ne_zero_iff t 0).2 ht₀
  have htr : traceRatio p = 0 := by
    unfold traceRatio
    rw [special_ray_trace_row_zero hp s hr 0, zero_div]
  have hT' : p.1.1 = projector (![1, 0] : Fin 2 → ℂ) := by
    have h : t = t 0 • (![1, 0] : Fin 2 → ℂ) := by
      funext i
      fin_cases i <;> simp [ht₁, Pi.smul_apply, smul_eq_mul]
    rw [hT, h, projector_scale _ ht₀]
  obtain ⟨d, hd, hD⟩ := exists_rep (source_subset_projective hp).1.2
  have hd' : ∃ j, d j ≠ 0 := by
    by_contra! h
    exact hd (funext h)
  obtain ⟨j, hj⟩ := hd'
  let v : Fin 6 → ℂ := fun i => p.1.2 i j
  have hvn : v j ≠ 0 := by
    change p.1.2 j j ≠ 0
    rw [hD, projector_diag_ne_zero_iff]
    exact hj
  have hv₁ : v 1 = 0 := by
    have h := pencil_incidence hp j 1 0 (fun q => by simp [pencil]; ring)
    rw [special_ray_trace_row_zero hp s hr 0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hT₀
  have hv₂ : v 2 = 0 := by
    have h := pencil_incidence hp j 2 1 (fun q => by simp [pencil]; ring)
    rw [special_ray_trace_row_zero hp s hr 0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hT₀
  let x := 3 * v 3 - v 0
  let y := 2 * v 3 - v 0
  let z := v 4
  let w := v 5
  have hV : alignedPencil p j = ![x, y, z, w] := by
    simp [alignedPencil, htr, x, y, z, w, v]
  let c : ℂ := ↑((PeriodicMPSProjectiveCoordinates.mass (ray s))⁻¹) * conj (ray s 3)
  have hc : c ≠ 0 := by
    apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (mass_pos _ (ray_ne_zero s)).ne'))
    simp [ray]
  have hF : alignedColumn p = c • ray s := by
    unfold alignedColumn
    rw [htr, neg_zero, shear_zero, hr, projector_column]
  have hq (i : Fin 8) : aligned x y z w i = aligned x y z w 3 * ray s i := by
    obtain ⟨hi, _⟩ := compact_relations hp hT₀ j i
    rw [hV, hF] at hi
    have hi' : aligned x y z w i * c = aligned x y z w 3 * (c * ray s i) := by
      simpa [quadrics, Pi.smul_apply, smul_eq_mul, show ray s 3 = 1 by simp [ray]] using hi
    rw [mul_left_comm (aligned x y z w 3) c] at hi'
    exact mul_left_cancel₀ hc ((mul_comm c _).trans hi')
  have hw : w = 0 := sq_eq_zero_iff.mp
    (by simpa [aligned, ray] using hq (6 : Fin 8))
  have hz : z ≠ 0 := by
    intro he
    obtain ⟨_, h⟩ := compact_relations hp hT₀ j 0
    rw [hV, hF] at h
    have hxy : x * y = 0 := (mul_eq_zero.mp (by
      simpa [relation, he, ray, Pi.smul_apply, smul_eq_mul] using h)).resolve_right hc
    have h0 : -x ^ 2 + 3 * x * y - y ^ 2 = 0 := by
      simpa [aligned, he, hw] using hq (0 : Fin 8)
    have hxy' : x = 0 ∧ y = 0 := by
      rcases mul_eq_zero.mp hxy with hx | hy
      · exact ⟨hx, sq_eq_zero_iff.mp (by simpa [hx] using h0)⟩
      · exact ⟨sq_eq_zero_iff.mp (by simpa [hy] using h0), hy⟩
    have h3 : v 3 = 0 := by
      dsimp only [x, y] at hxy'
      linear_combination hxy'.1 - hxy'.2
    have h0' : v 0 = 0 := by
      have hh := hxy'.1
      dsimp only [x] at hh
      rw [h3] at hh
      linear_combination -hh
    exact hvn (show v j = 0 by fin_cases j <;> assumption)
  have hq' : aligned x y z w = (z ^ 2) • ray s := by
    funext i
    simpa [Pi.smul_apply, smul_eq_mul, aligned, hw] using hq i
  obtain ⟨_, _, hy, hx⟩ := (ordinary_lifts s x y z w (z ^ 2) hs (pow_ne_zero _ hz)).mp hq'
  have hD' : p.1.2 = projector v := by
    have h := projector_column d j
    have hn : (↑((PeriodicMPSProjectiveCoordinates.mass d)⁻¹) * conj (d j) : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (mass_pos _ hd).ne'))
        ((map_ne_zero (starRingEnd ℂ)).2 hj)
    unfold v
    rw [hD, h, projector_scale _ hn]
  have hD'' : p.1.2 = projector ![2 * (x / z) - 3 * (y / z), 0, 0,
      x / z - y / z, 1, 0] := by
    rw [hD']
    have h : v = z • ![2 * (x / z) - 3 * (y / z), 0, 0, x / z - y / z, 1, 0] := by
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv₁, hv₂, show v 5 = 0 from hw]
      · dsimp only [x, y]
        field_simp [hz]
        ring
      · dsimp only [x, y]
        field_simp [hz]
        ring
      · rfl
    rw [h, projector_scale _ hz]
  have hA' : p.2 = projector (chart 0 (x / z) (y / z) 1 0) := by
    have he : aligned x y z w = (z ^ 2) • chart 0 (x / z) (y / z) 1 0 := by
      rw [chart, shear_zero, hw]
      funext i
      fin_cases i <;> simp [aligned, Pi.smul_apply, smul_eq_mul] <;> field_simp <;> ring
    have hh := congrArg projector (hq'.symm.trans he)
    rw [hr]
    simpa only [projector_scale _ (pow_ne_zero _ hz)] using hh
  have hh : p = affine (x / z) (y / z) 0 0 := by
    apply Prod.ext (Prod.ext hT' ?_) hA'
    simpa [affine] using hD''
  rcases hx with hx | hx
  · exact Or.inl (by simpa only [hx, hy] using hh)
  · exact Or.inr (by simpa only [hx, hy] using hh)

/-- The two trace-aligned points over each choice of sign. -/
def specialLift (s : ℂ) (second : Bool) : Ambient :=
  affine (if second then 3 * b s - root s else root s) (b s) 0 0

/-- The normalized observation whose compact fiber is computed here. -/
def specialObservation : Matrix (Fin 4) (Fin 4) ℂ :=
  (PeriodicMPSFiveSiteSpecialFiber.target.trace.re)⁻¹ • PeriodicMPSFiveSiteSpecialFiber.target

/-- Each of the four listed points is realized on the ordinary graph and
has the selected normalized observation. -/
theorem specialLift_mem (s : ℂ) (second : Bool) (hs : s = 1 ∨ s = -1) :
    specialLift s second ∈ source ∧ observation (specialLift s second) = specialObservation := by
  let x := if second then 3 * b s - root s else root s
  have hx : x = root s ∨ x = 3 * b s - root s := by cases second <;> simp [x]
  have ha : 2 * x - 3 * b s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    rcases hx with hx | hx <;> rcases hs with rfl | rfl <;>
      norm_num [hx, a, b, root, Complex.mul_re, Complex.sub_re, Complex.add_re,
        Complex.div_re, Complex.normSq_apply, pow_two] at he
  have hq : chart 0 x (b s) 1 0 = ray s := by
    rw [chart, shear_zero, ← one_smul ℂ (ray s)]
    exact (ordinary_lifts s x (b s) 1 0 1 hs one_ne_zero).mpr
      ⟨rfl, one_pow _, div_one _, by simpa only [div_one] using hx⟩
  have hgram : gram (ray s) = target := specialRay_gram s hs
  refine ⟨affine_mem_source x (b s) 0 0 ha, ?_⟩
  rw [observation_of_projector (ray_ne_zero s) (show (specialLift s second).2 = _ from
    congrArg projector hq), normalizedGram, PeriodicMPSFiveSiteNormalization.mass, hgram]
  rfl

/-- The selected marginal has no extra preimages on the compact boundary. -/
theorem compact_special_fiber_subset {p : Ambient} (hp : p ∈ source)
    (ho : observation p = specialObservation) :
    ∃ (s : ℂ) (second : Bool), (s = 1 ∨ s = -1) ∧ p = specialLift s second := by
  obtain ⟨q, hq, hP⟩ := exists_rep (source_amplitude_projective hp)
  rw [observation_of_projector hq hP] at ho
  obtain ⟨g, hg, hr⟩ := normalized_special_fiber q hq ho
  have hl (s : ℂ) (hs : s = 1 ∨ s = -1) (h : g • q = ray s) :
      ∃ second, p = specialLift s second := by
    have h' : p.2 = projector (ray s) := by rw [← h, projector_scale _ hg, hP]
    rcases lift_of_ray hp s hs h' with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  rcases hr with hr | hr
  · obtain ⟨second, he⟩ := hl 1 (Or.inl rfl) hr
    exact ⟨1, second, Or.inl rfl, he⟩
  · obtain ⟨second, he⟩ := hl (-1) (Or.inr rfl) hr
    exact ⟨-1, second, Or.inr rfl, he⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSpecialFiber
