import CFMPConvexFlatPrimitive270Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Matrix Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPActualFlatGraph269Transient

namespace CFMPActualFlatCoordinates271Transient

abbrev Chart := (Fin 5 → ℝ) × ℝ

def frameEquiv (q : Fin 6) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (frame q) (by fin_cases q <;> decide)

def join (u : Fin 5 → ℝ) (o : ℝ) : Lengths :=
  ![u 0, u 1, u 2, o, u 3, u 4]

def reassemble (q : Fin 6) (u : Fin 5 → ℝ) (o : ℝ) : Lengths :=
  fun j => join u o ((frameEquiv q).symm j)

theorem reassemble_frame (q : Fin 6) (u : Fin 5 → ℝ) (o : ℝ) (j : Fin 6) :
    reassemble q u o (frame q j) = join u o j := by
  change join u o ((frameEquiv q).symm (frameEquiv q j)) = _
  rw [Equiv.symm_apply_apply]

theorem fiveCoordinates_reassemble (q : Fin 6) (u : Fin 5 → ℝ) (o : ℝ) :
    fiveCoordinates (reassemble q u o) q = u := by
  funext j
  fin_cases j <;> simp [fiveCoordinates, reassemble_frame, join]

theorem reassemble_fiveCoordinates (q : Fin 6) (a : Lengths) :
    reassemble q (fiveCoordinates a q) (a (frame q 3)) = a := by
  funext j
  obtain ⟨i, hi⟩ := (frameEquiv q).surjective j
  change frame q i = j at hi
  rw [← hi, reassemble_frame]
  fin_cases i <;> rfl

/-- Signed height above the original flat graph. -/
def flatten (q : Fin 6) (a : Lengths) : Chart :=
  (fiveCoordinates a q, a (frame q 3) - lengthThreshold (fiveCoordinates a q))

def unflatten (q : Fin 6) (p : Chart) : Lengths :=
  reassemble q p.1 (p.2 + lengthThreshold p.1)

theorem flatten_unflatten (q : Fin 6) (p : Chart) :
    flatten q (unflatten q p) = p := by
  rcases p with ⟨u,r⟩
  simp [flatten, unflatten, fiveCoordinates_reassemble, reassemble_frame, join]

theorem unflatten_flatten (q : Fin 6) (a : Lengths) :
    unflatten q (flatten q a) = a := by
  simp only [unflatten, flatten, sub_add_cancel, reassemble_fiveCoordinates]

theorem fiveCoordinates_contDiff (q : Fin 6) :
    ContDiff ℝ ∞ (fun a : Lengths => fiveCoordinates a q) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;>
    dsimp [fiveCoordinates] <;>
    fun_prop

theorem reassemble_contDiff (q : Fin 6) :
    ContDiff ℝ ∞ (fun p : Chart => reassemble q p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  unfold reassemble
  generalize hi : (frameEquiv q).symm j = i
  fin_cases i <;>
    dsimp [join] <;>
    fun_prop

theorem flatten_contDiffAt (q : Fin 6) (a : Lengths) (ha : ∀ j, 0 < a j) :
    ContDiffAt ℝ ∞ (flatten q) a := by
  have hfive : ∀ j, 0 < fiveCoordinates a q j := by
    intro j
    fin_cases j <;> exact ha _
  have hbase := (fiveCoordinates_contDiff q).contDiffAt (x := a)
  have hheight : ContDiffAt ℝ ∞ (fun b : Lengths => b (frame q 3)) a := by fun_prop
  have hthreshold : ContDiffAt ℝ ∞
      (fun b : Lengths => lengthThreshold (fiveCoordinates b q)) a := by
    convert! ((lengthThreshold_contDiffAt (fiveCoordinates a q) hfive).comp a hbase) using 1
  change ContDiffAt ℝ ∞
    (fun b : Lengths => (fiveCoordinates b q,
      b (frame q 3) - lengthThreshold (fiveCoordinates b q))) a
  exact hbase.prodMk (hheight.sub hthreshold)

theorem unflatten_contDiffAt (q : Fin 6) (p : Chart) (hp : ∀ j, 0 < p.1 j) :
    ContDiffAt ℝ ∞ (unflatten q) p := by
  have ht : ContDiffAt ℝ ∞ (fun z : Chart => lengthThreshold z.1) p :=
    (lengthThreshold_contDiffAt p.1 hp).comp p contDiffAt_fst
  exact (reassemble_contDiff q).contDiffAt.comp p
    (contDiffAt_fst.prodMk (contDiffAt_snd.add ht))

theorem unflatten_positive (q : Fin 6) (p : Chart)
    (hp : ∀ j, 0 < p.1 j) (hh : 0 < p.2 + lengthThreshold p.1) :
    ∀ j, 0 < unflatten q p j := by
  have hjoin : ∀ i, 0 < join p.1 (p.2 + lengthThreshold p.1) i := by
    intro i
    fin_cases i <;> first | exact hp _ | exact hh
  intro j
  exact hjoin ((frameEquiv q).symm j)

/-- In the actual signed-height coordinates, the native closed flat sector is
exactly the upper halfspace; its boundary is included. -/
theorem native_sector_iff_nonneg (k : Fin 3) (p : Chart)
    (hp : ∀ j, 0 < p.1 j) (hh : 0 < p.2 + lengthThreshold p.1) :
    D5.S3.Geometry.Hyperideal.PositiveFlatClassification.Sector
      (fun q => Real.cosh (unflatten (k.castAdd 3) p q)) k ↔ 0 ≤ p.2 := by
  have hgraph := source_sector_graph (unflatten (k.castAdd 3) p)
    (unflatten_positive _ p hp hh) k
  have hheight : unflatten (k.castAdd 3) p (frame (k.castAdd 3) 3) =
      p.2 + lengthThreshold p.1 := by
    simp [unflatten, reassemble_frame, join]
  rw [show fiveCoordinates (unflatten (k.castAdd 3) p) (k.castAdd 3) = p.1 from
    fiveCoordinates_reassemble _ _ _, hheight] at hgraph
  constructor
  · intro h
    have hle := hgraph.mp h
    linarith
  · intro h
    apply hgraph.mpr
    linarith

end CFMPActualFlatCoordinates271Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualFlatCoordinates271Transient.flatten_unflatten,
      ``CFMPActualFlatCoordinates271Transient.unflatten_flatten,
      ``CFMPActualFlatCoordinates271Transient.flatten_contDiffAt,
      ``CFMPActualFlatCoordinates271Transient.unflatten_contDiffAt,
      ``CFMPActualFlatCoordinates271Transient.native_sector_iff_nonneg] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP271 actual flat-interface coordinates absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP271 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP271 CHECKED {name} axioms={axioms}"
