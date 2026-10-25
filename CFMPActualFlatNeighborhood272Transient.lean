import CFMPActualFlatCoordinates271Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine sourceCosine_continuousAt)
open CFMPActualExtendedAngle268Transient (positiveLengths positiveLengths_open)
open CFMPActualFlatCoordinates271Transient
open CFMPActualFlatGraph269Transient (fiveCoordinates source_sector_graph)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Genuine Sector positive_classification)

namespace CFMPActualFlatNeighborhood272Transient

/-- Near a point in a native closed flat sector, all the other flat sectors
are excluded by strict continuous cosine inequalities. The genuine side is
therefore exactly the negative signed-height side in the actual coordinates. -/
theorem genuine_signed_height_eventually (a : Lengths) (ha : ∀ j, 0 < a j)
    (k : Fin 3) (hk : Sector (fun q => Real.cosh (a q)) k) :
    ∀ᶠ b in 𝓝 a, genuine b ↔ (flatten (k.castAdd 3) b).2 < 0 := by
  have hcosh (j : Fin 6) : 1 < Real.cosh (a j) := Real.one_lt_cosh.mpr (ha j).ne'
  have hng : ¬ Genuine (fun q => Real.cosh (a q)) := by
    intro hg
    exact (not_le_of_gt (hg (k.castAdd 3)).1) hk
  obtain ⟨i, hi, hunique⟩ :=
    (positive_classification (fun q => Real.cosh (a q)) hcosh).2.1.resolve_left hng
  have hother (j : Fin 3) (hjk : j ≠ k) :
      -1 < sourceCosine a (j.castAdd 3) := by
    apply lt_of_not_ge
    intro hj
    exact hjk ((hunique j hj).trans (hunique k hk).symm)
  have hpositive : ∀ᶠ b in 𝓝 a, b ∈ positiveLengths :=
    positiveLengths_open.mem_nhds ha
  have hexclude : ∀ᶠ b in 𝓝 a,
      ∀ j : Fin 3, j ≠ k → ¬ Sector (fun q => Real.cosh (b q)) j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall (fun _ hne => False.elim (hne hjk))
    · have he := (sourceCosine_continuousAt a ha (j.castAdd 3)).eventually
        (Ioi_mem_nhds (hother j hjk))
      filter_upwards [he] with b hb
      intro _ hj
      exact (not_le_of_gt hb) hj
  filter_upwards [hpositive, hexclude] with b hb he
  have hsector : Sector (fun q => Real.cosh (b q)) k ↔
      0 ≤ (flatten (k.castAdd 3) b).2 := by
    simpa only [flatten, sub_nonneg] using source_sector_graph b hb k
  constructor
  · intro hg
    apply lt_of_not_ge
    intro hr
    exact (not_le_of_gt (hg.2 (k.castAdd 3)).1) (hsector.mpr hr)
  · intro hr
    refine ⟨hb, ?_⟩
    rcases (positive_classification (fun q => Real.cosh (b q))
      (fun j => Real.one_lt_cosh.mpr (hb j).ne')).2.1 with hg | ⟨j, hj, _⟩
    · exact hg
    · by_cases hjk : j = k
      · subst j
        exact False.elim ((not_le_of_gt hr) (hsector.mp hj))
      · exact False.elim (he j hjk hj)

/-- The preceding native neighborhood transported by the actual smooth chart.
No implicit assertion about all negative heights is made. -/
theorem chart_genuine_eventually (a : Lengths) (ha : ∀ j, 0 < a j)
    (k : Fin 3) (hk : Sector (fun q => Real.cosh (a q)) k) :
    ∀ᶠ p in 𝓝 (flatten (k.castAdd 3) a),
      genuine (unflatten (k.castAdd 3) p) ↔ p.2 < 0 := by
  have hp : ∀ j, 0 < (flatten (k.castAdd 3) a).1 j := by
    intro j
    fin_cases j <;> exact ha _
  have hc : ContinuousAt (unflatten (k.castAdd 3)) (flatten (k.castAdd 3) a) :=
    (unflatten_contDiffAt _ _ hp).continuousAt
  have hnear : ∀ᶠ b in 𝓝 (unflatten (k.castAdd 3) (flatten (k.castAdd 3) a)),
      genuine b ↔ (flatten (k.castAdd 3) b).2 < 0 := by
    simpa only [unflatten_flatten] using genuine_signed_height_eventually a ha k hk
  have he := hc.eventually hnear
  filter_upwards [he] with p h
  simpa only [flatten_unflatten] using h

end CFMPActualFlatNeighborhood272Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualFlatNeighborhood272Transient.genuine_signed_height_eventually,
      ``CFMPActualFlatNeighborhood272Transient.chart_genuine_eventually] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP272 native genuine-side neighborhood absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP272 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP272 CHECKED {name} axioms={axioms}"
