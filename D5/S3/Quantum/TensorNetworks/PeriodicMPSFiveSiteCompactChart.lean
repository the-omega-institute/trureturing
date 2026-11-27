/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteTraceChart]
   utility: none
   digest: Ordinary points of the compact trace graph admit aligned affine coordinates. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactIncidence
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteTraceChart

/-! The trace frame and the projective mixed coefficient give explicit coordinates
near the four points of the selected fiber. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart

open Set Filter PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteTraceChart
  PeriodicMPSFiveSiteCompactSource PeriodicMPSProjectiveCoordinates
open scoped Topology

open private traceDirection pencil
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource

noncomputable section

private theorem chart_scale (s r x y z w : ℂ) :
    chart s (r * x) (r * y) (r * z) (r * w) = r ^ 2 • chart s x y z w := by
  have h : aligned (r * x) (r * y) (r * z) (r * w) = r ^ 2 • aligned x y z w := by
    funext i
    fin_cases i <;> simp [aligned, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [chart, h, shear_smul, ← chart]

/-- Projector coordinates for the ordinary affine chart with aligned mixed
coefficient equal to one. -/
def affine (x y w s : ℂ) : Ambient :=
  let a := 2 * x - 3 * y
  let d := x - y
  ((projector ![1, s],
    projector ![a, a * s, a * s ^ 2, d, 1 + 2 * s * d, w + s + s ^ 2 * d]),
    projector (chart s x y 1 w))

set_option maxHeartbeats 2000000 in
-- The trace frame and six projective coordinates are verified symbolically.
/-- An ordinary point with first trace and aligned mixed coefficient nonzero
has the indicated affine coordinates. -/
theorem ordinary_eq_affine (u : Inputs) (ht : u.val 0 ≠ 0)
    (s : ℂ) (hs : u.val 1 = u.val 0 * s)
    (z : ℂ) (hz : z = u.val 0 * u.val 1 - u.val 4 - 2 * s * u.val 2)
    (hn : z ≠ 0) :
    ordinary u = affine ((3 * u.val 2 - u.val 0 ^ 2) / z)
      ((2 * u.val 2 - u.val 0 ^ 2) / z)
      ((u.val 3 - s * z - s ^ 2 * u.val 2) / z) s := by
  let t := u.val 0
  let d := u.val 2
  let e := u.val 3
  let m := t * u.val 1 - u.val 4
  let a := t ^ 2
  let x := (3 * d - a) / z
  let y := (2 * d - a) / z
  let w := (e - s * z - s ^ 2 * d) / z
  have ha : 2 * x - 3 * y = a / z := by
    dsimp [x, y]
    field_simp
    ring
  have hd : x - y = d / z := by
    dsimp [x, y]
    field_simp
    ring
  have htrace : traceDirection u.val = t • ![1, s] := by
    funext j
    fin_cases j <;> simp [traceDirection, t, hs, Pi.smul_apply, smul_eq_mul]
  have hpencil : pencil u.val = z • ![a / z, a / z * s, a / z * s ^ 2, d / z,
      1 + 2 * s * (d / z), w + s + s ^ 2 * (d / z)] := by
    funext i
    fin_cases i <;> simp [pencil, a, w, t, d, e, hs, Pi.smul_apply, smul_eq_mul] <;>
      field_simp <;> try ring
    linear_combination -hz - u.val 0 * hs
  have hframe :
      frame 1 s a d m e = chart s (3 * d - a) (2 * d - a) z (e - s * z - s ^ 2 * d) := by
    have hm : z + 2 * s * d = m := by dsimp [d, m, t]; rw [hz]; ring
    have he : e - s * z - s ^ 2 * d + s * z + s ^ 2 * d = e := by ring
    have h := frame_first_chart s a d z (e - s * z - s ^ 2 * d)
    rw [hm, he] at h
    exact h
  have hp : coordinates t (u.val 1) d e (u.val 4) = (t * z ^ 2) • chart s x y 1 w := by
    have hk : t ^ 2 * s - m = u.val 4 := by dsimp [m, t]; rw [hs]; ring
    have h1 : coordinates t (u.val 1) d e (u.val 4) = t • frame 1 s a d m e := by
      have h := frame_trace_coordinates t 1 s d m e
      simp only [mul_one] at h
      rw [hk, ← hs] at h
      exact h
    have h2 : chart s (3 * d - a) (2 * d - a) z (e - s * z - s ^ 2 * d) =
        z ^ 2 • chart s x y 1 w := by
      have h := chart_scale s z x y 1 w
      simp only [x, y, w, mul_div_cancel₀ _ hn, mul_one] at h
      exact h
    rw [h1, hframe, h2, smul_smul]
  change ordinary u = affine x y w s
  unfold ordinary affine
  rw [ha, hd, htrace, hpencil, hp, projector_scale _ ht, projector_scale _ hn,
    projector_scale _ (mul_ne_zero ht (pow_ne_zero _ hn))]

private theorem chart_ne_zero (s x y w : ℂ) : chart s x y 1 w ≠ 0 := by
  intro h
  have he := congrArg (shear (-s)) h
  have hz : shear (-s) (0 : Fin 8 → ℂ) = 0 := by
    funext i
    fin_cases i <;> simp [shear]
  rw [chart, shear_add, neg_add_cancel, shear_zero, hz] at he
  exact one_ne_zero ((aligned_eq_zero_iff x y 1 w).1 he).2.1

set_option maxHeartbeats 2000000 in
-- The witness uses vector literals and the full five-site frame formula.
/-- Each point in this affine chart with nonzero squared trace is represented
by ordinary complex trace coordinates. -/
theorem affine_mem_ordinary (x y w s : ℂ) (ha : 2 * x - 3 * y ≠ 0) :
    affine x y w s ∈ range ordinary := by
  let a := 2 * x - 3 * y
  let d := x - y
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by decide)
  have ht' : t ≠ 0 := fun h => ha (by simpa [h, a] using ht.symm)
  let q : Fin 5 → ℂ := ![t, t * s, d, w + s + s ^ 2 * d, a * s - (1 + 2 * s * d)]
  have hframe := frame_first_chart s a d 1 w
  rw [mul_one s] at hframe
  have hx : 3 * d - a = x := by dsimp [d, a]; ring
  have hy : 2 * d - a = y := by dsimp [d, a]; ring
  have hq : coordinates (q 0) (q 1) (q 2) (q 3) (q 4) = t • chart s x y 1 w := by
    change coordinates t (t * s) d (w + s + s ^ 2 * d) (a * s - (1 + 2 * s * d)) = _
    have h := frame_trace_coordinates t 1 s d (1 + 2 * s * d) (w + s + s ^ 2 * d)
    simp only [mul_one] at h
    rw [ht, hframe, hx, hy] at h
    exact h
  have hqn : coordinates (q 0) (q 1) (q 2) (q 3) (q 4) ≠ 0 := by
    rw [hq]
    exact smul_ne_zero ht' (chart_ne_zero s x y w)
  let u : Inputs := ⟨q, hqn⟩
  have hs : u.val 1 = u.val 0 * s := rfl
  have hz : (1 : ℂ) = u.val 0 * u.val 1 - u.val 4 - 2 * s * u.val 2 := by
    change (1 : ℂ) = t * (t * s) - (a * s - (1 + 2 * s * d)) - 2 * s * d
    linear_combination -s * ht
  have h := ordinary_eq_affine u ht' s hs 1 hz one_ne_zero
  have he : w + s + s ^ 2 * d - s * 1 - s ^ 2 * d = w := by ring
  change ordinary u = affine ((3 * d - t ^ 2) / 1) ((2 * d - t ^ 2) / 1)
    ((w + s + s ^ 2 * d - s * 1 - s ^ 2 * d) / 1) s at h
  rw [ht, hx, hy, he, div_one, div_one, div_one] at h
  exact ⟨u, h⟩

theorem affine_mem_source (x y w s : ℂ) (ha : 2 * x - 3 * y ≠ 0) :
    affine x y w s ∈ source :=
  subset_closure (affine_mem_ordinary x y w s ha)

/-- The affine chart is inverted from the trace direction and the ratios of
the squared trace and determinant pencil. -/
def affineInverse (p : Ambient) : Fin 4 → ℂ :=
  let T := p.1.1
  let P := p.1.2
  let s := T 1 0 / T 0 0
  let a := P 0 4 / P 4 4
  let d := P 3 4 / P 4 4
  let e := P 5 4 / P 4 4
  let z := 1 - 2 * s * d
  ![(3 * d - a) / z, (2 * d - a) / z, (e - s + s ^ 2 * d) / z, s]

set_option maxHeartbeats 1000000 in
-- Reduce the projector ratios before simplifying the affine coordinate changes.
theorem affineInverse_affine (x y w s : ℂ) (hm : 1 + 2 * s * (x - y) ≠ 0) :
    affineInverse (affine x y w s) = ![x, y, w, s] := by
  let a := 2 * x - 3 * y
  let d := x - y
  let m := 1 + 2 * s * d
  let t : Fin 2 → ℂ := ![1, s]
  let p : Fin 6 → ℂ := ![a, a * s, a * s ^ 2, d, m, w + s + s ^ 2 * d]
  have ht : projector t 1 0 / projector t 0 0 = s := by
    rw [projector_ratio t 1 0 (show t 0 ≠ 0 from one_ne_zero)]
    change s / 1 = s
    exact div_one s
  have hap : projector p 0 4 / projector p 4 4 = a / m :=
    projector_ratio p 0 4 hm
  have hdp : projector p 3 4 / projector p 4 4 = d / m :=
    projector_ratio p 3 4 hm
  have hep : projector p 5 4 / projector p 4 4 = (w + s + s ^ 2 * d) / m :=
    projector_ratio p 5 4 hm
  change ![(3 * (projector p 3 4 / projector p 4 4) -
      projector p 0 4 / projector p 4 4) /
      (1 - 2 * (projector t 1 0 / projector t 0 0) * (projector p 3 4 / projector p 4 4)),
    (2 * (projector p 3 4 / projector p 4 4) - projector p 0 4 / projector p 4 4) /
      (1 - 2 * (projector t 1 0 / projector t 0 0) * (projector p 3 4 / projector p 4 4)),
    (projector p 5 4 / projector p 4 4 - projector t 1 0 / projector t 0 0 +
      (projector t 1 0 / projector t 0 0) ^ 2 * (projector p 3 4 / projector p 4 4)) /
      (1 - 2 * (projector t 1 0 / projector t 0 0) * (projector p 3 4 / projector p 4 4)),
    projector t 1 0 / projector t 0 0] = _
  rw [ht, hap, hdp, hep]
  have hz : 1 - 2 * s * (d / m) = 1 / m := by
    field_simp [show m ≠ 0 from hm]
    dsimp [m]
    ring
  rw [hz]
  funext i
  fin_cases i <;> simp <;>
    field_simp [show m ≠ 0 from hm] <;> dsimp [a, d, m] <;> ring

private def fromFour (q : Fin 4 → ℂ) : Ambient := affine (q 0) (q 1) (q 2) (q 3)

private theorem continuous_fromFour : Continuous fromFour := by
  rw [continuous_iff_continuousAt]
  intro q
  let a : (Fin 4 → ℂ) → ℂ := fun q => 2 * q 0 - 3 * q 1
  let d : (Fin 4 → ℂ) → ℂ := fun q => q 0 - q 1
  let T : (Fin 4 → ℂ) → Fin 2 → ℂ := fun q => ![1, q 3]
  let P : (Fin 4 → ℂ) → Fin 6 → ℂ := fun q =>
    ![a q, a q * q 3, a q * q 3 ^ 2, d q, 1 + 2 * q 3 * d q, q 2 + q 3 + q 3 ^ 2 * d q]
  let A : (Fin 4 → ℂ) → Fin 8 → ℂ := fun q => chart (q 3) (q 0) (q 1) 1 (q 2)
  have hT : T q ≠ 0 := fun e => one_ne_zero (congrFun e 0)
  have hP : P q ≠ 0 := by
    intro h
    have hd : d q = 0 := congrFun h 3
    have hm : 1 + 2 * q 3 * d q = 0 := congrFun h 4
    simp [hd] at hm
  have hA : A q ≠ 0 := chart_ne_zero _ _ _ _
  have cT : Continuous T := continuous_pi fun i => by fin_cases i <;> simp [T] <;> fun_prop
  have cP : Continuous P := continuous_pi fun i => by fin_cases i <;> simp [P, a, d] <;> fun_prop
  have cA : Continuous A := continuous_pi fun i => by
    fin_cases i <;> simp [A, chart, shear, aligned] <;> fun_prop
  exact (((continuousAt_projector hT).comp cT.continuousAt).prodMk
    ((continuousAt_projector hP).comp cP.continuousAt)).prodMk
    ((continuousAt_projector hA).comp cA.continuousAt)

private def traceRatio (p : Ambient) : ℂ := p.1.1 1 0 / p.1.1 0 0

private def pencilRatio (p : Ambient) (j : Fin 6) : ℂ := p.1.2 j 4 / p.1.2 4 4

private def mixedRatio (p : Ambient) : ℂ := 1 - 2 * traceRatio p * pencilRatio p 3

private def ambientDomain : Set Ambient :=
  {p | p.1.1 0 0 ≠ 0 ∧ p.1.2 4 4 ≠ 0 ∧ mixedRatio p ≠ 0 ∧ pencilRatio p 0 ≠ 0}

private theorem continuousAt_traceRatio {p : Ambient} (hp : p.1.1 0 0 ≠ 0) :
    ContinuousAt traceRatio p := by
  unfold traceRatio
  exact (by fun_prop : ContinuousAt (fun q : Ambient => q.1.1 1 0) p).div (by fun_prop) hp

private theorem continuousAt_pencilRatio {p : Ambient} (hp : p.1.2 4 4 ≠ 0) (j : Fin 6) :
    ContinuousAt (fun q => pencilRatio q j) p := by
  unfold pencilRatio
  exact (by fun_prop : ContinuousAt (fun q : Ambient => q.1.2 j 4) p).div (by fun_prop) hp

private theorem continuousAt_mixedRatio {p : Ambient}
    (ht : p.1.1 0 0 ≠ 0) (hp : p.1.2 4 4 ≠ 0) : ContinuousAt mixedRatio p := by
  unfold mixedRatio
  exact continuousAt_const.sub ((continuousAt_const.mul (continuousAt_traceRatio ht)).mul
    (continuousAt_pencilRatio hp 3))

private theorem isOpen_ambientDomain : IsOpen ambientDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have ht : ContinuousAt (fun q : Ambient => q.1.1 0 0) p := by fun_prop
  have hd : ContinuousAt (fun q : Ambient => q.1.2 4 4) p := by fun_prop
  have hT : ∀ᶠ q in 𝓝 p, q.1.1 0 0 ≠ 0 := ht (isOpen_ne.mem_nhds hp.1)
  have hD : ∀ᶠ q in 𝓝 p, q.1.2 4 4 ≠ 0 := hd (isOpen_ne.mem_nhds hp.2.1)
  have hM : ∀ᶠ q in 𝓝 p, mixedRatio q ≠ 0 :=
    continuousAt_mixedRatio hp.1 hp.2.1 (isOpen_ne.mem_nhds hp.2.2.1)
  have hA : ∀ᶠ q in 𝓝 p, pencilRatio q 0 ≠ 0 :=
    continuousAt_pencilRatio hp.2.1 0 (isOpen_ne.mem_nhds hp.2.2.2)
  exact hT.and (hD.and (hM.and hA))

private theorem continuousAt_affineInverse {p : Ambient} (hp : p ∈ ambientDomain) :
    ContinuousAt affineInverse p := by
  have ht := continuousAt_traceRatio hp.1
  have hd := continuousAt_pencilRatio hp.2.1 3
  have ha := continuousAt_pencilRatio hp.2.1 0
  have he := continuousAt_pencilRatio hp.2.1 5
  have hm := continuousAt_mixedRatio hp.1 hp.2.1
  apply continuousAt_pi.mpr
  intro j
  fin_cases j
  · exact ((continuousAt_const.mul hd).sub ha).div hm hp.2.2.1
  · exact ((continuousAt_const.mul hd).sub ha).div hm hp.2.2.1
  · exact ((he.sub ht).add ((ht.pow 2).mul hd)).div hm hp.2.2.1
  · exact ht

set_option maxHeartbeats 1500000 in
-- The ratio of the aligned and ambient mixed coefficients determines the affine domain.
private theorem ordinary_round_trip (u : Inputs) (hu : ordinary u ∈ ambientDomain) :
    fromFour (affineInverse (ordinary u)) = ordinary u := by
  let t := u.val 0
  let d := u.val 2
  let s := u.val 1 / t
  let m := t * u.val 1 - u.val 4
  let z := m - 2 * s * d
  have ht : t ≠ 0 := (projector_diag_ne_zero_iff (traceDirection u.val) 0).mp hu.1
  have hm : m ≠ 0 := (projector_diag_ne_zero_iff (pencil u.val) 4).mp hu.2.1
  have hs : u.val 1 = t * s := (mul_div_cancel₀ _ ht).symm
  have htr : traceRatio (ordinary u) = s := projector_ratio (traceDirection u.val) 1 0 ht
  have hdr : pencilRatio (ordinary u) 3 = d / m := projector_ratio (pencil u.val) 3 4 hm
  have hzratio : mixedRatio (ordinary u) = z / m := by
    rw [mixedRatio, htr, hdr]
    dsimp only [z]
    field_simp [hm]
  have hz : z ≠ 0 := by
    intro h
    have he := hu.2.2.1
    rw [hzratio, h, zero_div] at he
    exact he rfl
  let x := (3 * d - t ^ 2) / z
  let y := (2 * d - t ^ 2) / z
  let w := (u.val 3 - s * z - s ^ 2 * d) / z
  have hxy : x - y = d / z := by
    dsimp only [x, y]
    field_simp [hz]
    ring
  have hmn : 1 + 2 * s * (x - y) = m / z := by
    rw [hxy]
    field_simp [hz]
    dsimp only [z]
    ring
  have h := ordinary_eq_affine u ht s hs z rfl hz
  change ordinary u = affine x y w s at h
  rw [h, affineInverse_affine _ _ _ _ (hmn.symm ▸ div_ne_zero hm hz)]
  rfl

/-- Closure of the graph adds no extra points on the open ordinary affine chart. -/
theorem affine_round_trip_of_source {p : Ambient} (hp : p ∈ source) (hchart : p ∈ ambientDomain) :
    fromFour (affineInverse p) = p := by
  have hp' : p ∈ closure (range ordinary) := hp
  haveI : NeBot (𝓝[range ordinary] p) := mem_closure_iff_nhdsWithin_neBot.mp hp'
  have h₁ := (continuous_fromFour.continuousAt.comp
    (continuousAt_affineInverse hchart)).continuousWithinAt (s := range ordinary)
  have h₂ : Tendsto (fun t : Ambient => t) (𝓝[range ordinary] p) (𝓝 p) :=
    nhdsWithin_le_nhds
  have he : (fun t => fromFour (affineInverse t)) =ᶠ[𝓝[range ordinary] p] fun t => t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ambientDomain.mem_nhds hchart)] with q hq hq'
    obtain ⟨u, rfl⟩ := hq
    exact ordinary_round_trip u hq'
  exact tendsto_nhds_unique h₁ (h₂.congr' he.symm)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart
