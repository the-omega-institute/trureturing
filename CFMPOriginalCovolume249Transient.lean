import CFMPOriginalNormalizedSchlafli248Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicTopology D5.S3.Geometry.HyperbolicNormalizedDensity
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPActualNativeMass435Transient
open CFMPOriginalPhysicalEdge237Transient CFMPAnchoredPhysical239Transient
open CFMPOriginalBoundaryEdge229Transient CFMPPairedSupportConormal230Transient

namespace CFMPOriginalCovolume249Transient

private local instance : MeasurableSpace Coordinates3 := borel _
private local instance : BorelSpace Coordinates3 := ⟨rfl⟩
private local instance : MeasurableSpace Native3 := borel _
private local instance : BorelSpace Native3 := ⟨rfl⟩

theorem source_angle_hasDerivAt
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (q : Fin 6) (hc : -1 < sourceCosine l0 q ∧ sourceCosine l0 q < 1) :
    HasDerivAt (fun s => sourceAngle (l s) q)
      (deriv (fun s => sourceAngle (l s) q) t) t := by
  subst l0
  let M : ℝ → M4 := fun s => frame M0 (l s)
  let dN : Fin 20 → Fin 4 → ℝ := fun n =>
    deriv (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n) t
  obtain ⟨hpos,hinv,hG⟩ := frame_path_geometry (l t) hl0 M0 hm0 hg0
    l t hl.continuousAt rfl
  have hN (n : Fin 20) (i : Fin 4) :
      HasDerivAt (fun s =>
        CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i) (dN n i) t := by
    have hn := CFMPOriginalNormalDerivative435Transient.actual_normal_derivative
      (l t) hl0 M0 hm0 hg0 f hf l dl t hl rfl n
    exact hasDerivAt_pi.mp hn.2.2.1 i
  let N := fun s => CFMPOriginalExteriorNativeNormal435Transient.unit
    (l s) (M s) (pairs (physical q)).1.1
  let R := fun s => CFMPOriginalExteriorNativeNormal435Transient.unit
    (l s) (M s) (pairs (physical q)).2.1
  have hd := lorentz_hasDerivAt N R (dN (pairs (physical q)).1.1)
    (dN (pairs (physical q)).2.1) t (hN _) (hN _)
  have hcos : (fun s => sourceCosine (l s) q) =ᶠ[𝓝 t]
      fun s => -lorentz (N s) (R s) := by
    filter_upwards [hpos,hinv,hG] with s hp hi hg
    exact (actual_physical_cosine (l s) hp (M s) hi hg q).symm
  have hdiff := hd.neg.differentiableAt.congr_of_eventuallyEq hcos
  exact ((Real.differentiableAt_arccos.mpr ⟨hc.1.ne',hc.2.ne⟩).comp t hdiff).hasDerivAt

theorem original_same_family_covolume
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → (Fin 6 → ℝ)) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : ContDiffAt ℝ 1 l t) (hdl : HasDerivAt l dl t) (hbase : l t = l0)
    (hgen : CFMPGenuineLengthNeighborhood435Transient.genuine l0)
    (P : ℝ → M4) (g : ∀ s, cutBody (l s) → HyperbolicThreeSpace)
    (hfamily : ∀ᶠ s in 𝓝 t,
      (∀ i j, lorentz (P s i) (P s j) = lengthGram (l s) i j) ∧
      Function.Injective (g s) ∧ IsCompact (range (g s)) ∧
      (∀ w : cutBody (l s), ∃ y : Fin 4 → ℝ,
        y = (radial (l s) w.val) ᵥ* P s ∧ lorentz y y = -1 ∧ 0 < y 3 ∧
        (g s w).coordinates.val = WithLp.toLp 2
          (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))) :
    HasDerivAt
      (fun s => 2 * ((Measure.euclideanHausdorffMeasure 3 : Measure Native3)
          (range (g s))).toReal + ∑ q : Fin 6, l s q * sourceAngle (l s) q)
      (∑ q : Fin 6, sourceAngle l0 q * dl q) t := by
  have hV := CFMPOriginalNormalizedSchlafli248Transient.original_normalized_schlafli
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hdl hbase hgen P g hfamily
  have hangle (q : Fin 6) := source_angle_hasDerivAt
    l0 hl0 M0 hm0 hg0 f hf l dl t hdl hbase q (hgen.2 q)
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 6)))
    (fun q _ => (hasDerivAt_pi.mp hdl q).mul (hangle q))
  have hc := (hV.const_mul 2).add hsum
  have he :
      2 * (-(1/2 : ℝ) * ∑ q : Fin 6, l0 q * deriv (fun s => sourceAngle (l s) q) t) +
        (∑ q : Fin 6, (dl q * sourceAngle (l t) q +
          l t q * deriv (fun s => sourceAngle (l s) q) t)) =
      ∑ q : Fin 6, sourceAngle l0 q * dl q := by
    rw [hbase,Finset.sum_add_distrib]
    calc
      _ = ∑ q : Fin 6, dl q * sourceAngle l0 q := by ring
      _ = _ := Finset.sum_congr rfl (fun q _ => mul_comm _ _)
  convert! hc using 1 <;> simp only [Pi.add_apply, Pi.mul_apply, he]

end CFMPOriginalCovolume249Transient

run_cmd do
  let name := ``CFMPOriginalCovolume249Transient.original_same_family_covolume
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP249 original same-family covolume absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP249 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP249 CHECKED {name} axioms={axioms}"
