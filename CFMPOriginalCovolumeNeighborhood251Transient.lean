import CFMPOriginalCovolume249Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalAnchoredFamily435Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicTopology D5.S3.Geometry.HyperbolicNormalizedDensity
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalPhysicalEdge237Transient CFMPOriginalCovolume249Transient

namespace CFMPOriginalCovolumeNeighborhood251Transient

abbrev Lengths := Fin 6 → ℝ
abbrev RealizationFamily := ∀ a : Lengths, cutBody a → HyperbolicThreeSpace

private local instance : MeasurableSpace Native3 := borel _
private local instance : BorelSpace Native3 := ⟨rfl⟩

def physicalVolume (G : RealizationFamily) (a : Lengths) : ℝ :=
  ((Measure.euclideanHausdorffMeasure 3 : Measure Native3) (range (G a))).toReal

def physicalCovolume (G : RealizationFamily) (a : Lengths) : ℝ :=
  2 * physicalVolume G a + ∑ q : Fin 6, a q * sourceAngle a q

def realizationContract (M0 : Matrix (Fin 4) (Fin 4) ℝ)
    (G : RealizationFamily) (a : Lengths) : Prop :=
  (∀ i, 0 < a i) ∧ (frame M0 a).det ≠ 0 ∧
    (∀ i j, lorentz (frame M0 a i) (frame M0 a j) = lengthGram a i j) ∧
    Continuous (G a) ∧ Function.Injective (G a) ∧ IsCompact (range (G a)) ∧
    ∀ w : cutBody a, ∃ y : Fin 4 → ℝ,
      y = (radial a w.val) ᵥ* frame M0 a ∧ lorentz y y = -1 ∧ 0 < y 3 ∧
      (G a w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))

theorem exists_original_covolume_neighborhood
    (l0 : Lengths) (hl0 : ∀ i, 0 < l0 i)
    (M0 : Matrix (Fin 4) (Fin 4) ℝ) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (hgen : CFMPGenuineLengthNeighborhood435Transient.genuine l0) :
    ∃ (U : Set Lengths) (G : RealizationFamily),
      l0 ∈ U ∧ IsOpen U ∧
      (∀ a ∈ U, CFMPGenuineLengthNeighborhood435Transient.genuine a) ∧
      ContDiffOn ℝ ∞ (frame M0) U ∧ frame M0 l0 = M0 ∧ G l0 = f ∧
      (∀ a ∈ U, realizationContract M0 G a) ∧
      ∀ (l : ℝ → Lengths) (dl : Lengths) (t : ℝ),
        ContDiffAt ℝ 1 l t → HasDerivAt l dl t → l t ∈ U →
        HasDerivAt (fun s => physicalCovolume G (l s))
          (∑ q : Fin 6, sourceAngle (l t) q * dl q) t := by
  classical
  obtain ⟨V,h0,g,hV,hsm,hanchor,hfanchor,hgeom⟩ :=
    CFMPOriginalAnchoredFamily435Transient.exists_original_anchored_family
      l0 hl0 M0 hm0 hg0 f hf
  let U : Set Lengths := V ∩ {a | CFMPGenuineLengthNeighborhood435Transient.genuine a}
  have hU : IsOpen U := hV.inter CFMPGenuineLengthNeighborhood435Transient.genuine_open
  have h0U : l0 ∈ U := ⟨h0,hgen⟩
  let p0 : HyperbolicThreeSpace := f ⟨(fun _ => 1/4),(shared_radial_body l0 hl0).2.1⟩
  let G : RealizationFamily := fun a =>
    if ha : a ∈ V then g ⟨a,ha⟩ else fun _ => p0
  have hGa (a : Lengths) (ha : a ∈ V) : G a = g ⟨a,ha⟩ := by
    dsimp only [G]
    rw [dif_pos ha]
  have hcontract (a : Lengths) (ha : a ∈ U) : realizationContract M0 G a := by
    simpa only [realizationContract,hGa a ha.1] using hgeom ⟨a,ha.1⟩
  refine ⟨U,G,h0U,hU,(fun a ha => ha.2),hsm.mono inter_subset_left,hanchor,?_,hcontract,?_⟩
  · rw [hGa l0 h0]
    exact hfanchor
  · intro l dl t hl hdl ht
    have hbase := hcontract (l t) ht
    have hrows := hbase.2.2.1
    have hgbase : frame M0 (l t) * J * (frame M0 (l t)).transpose =
        lengthGram (l t) := by
      ext i j
      simpa [J,Matrix.mul_apply,lorentz,Fin.sum_univ_four] using hrows i j
    have hnear : ∀ᶠ s in 𝓝 t, l s ∈ U :=
      hdl.continuousAt.eventually (hU.mem_nhds ht)
    have hfamily : ∀ᶠ s in 𝓝 t,
        (∀ i j, lorentz (frame M0 (l s) i) (frame M0 (l s) j) = lengthGram (l s) i j) ∧
        Function.Injective (G (l s)) ∧ IsCompact (range (G (l s))) ∧
        (∀ w : cutBody (l s), ∃ y : Fin 4 → ℝ,
          y = (radial (l s) w.val) ᵥ* frame M0 (l s) ∧ lorentz y y = -1 ∧ 0 < y 3 ∧
          (G (l s) w).coordinates.val = WithLp.toLp 2
            (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) := by
      filter_upwards [hnear] with s hs
      have h := hcontract (l s) hs
      exact ⟨h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
    have hd := CFMPOriginalCovolume249Transient.original_same_family_covolume
      (l t) hbase.1 (frame M0 (l t)) hbase.2.1 hgbase (G (l t))
      hbase.2.2.2.2.2.2 l dl t hl hdl rfl ht.2
      (fun s => frame M0 (l s)) (fun s => G (l s)) hfamily
    simpa only [physicalCovolume,physicalVolume] using hd

end CFMPOriginalCovolumeNeighborhood251Transient

run_cmd do
  let name := ``CFMPOriginalCovolumeNeighborhood251Transient.exists_original_covolume_neighborhood
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP251 original covolume neighborhood absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP251 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP251 CHECKED {name} axioms={axioms}"
