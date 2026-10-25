import CFMPActualEverywhereLocalPrimitive276Transient
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology unitInterval

namespace CFMPLocalExactRectangle277Transient

abbrev Plane := ℝ × ℝ
def square : Set Plane := Icc 0 1 ×ˢ Icc 0 1

/-- A continuous covector with a local primitive at every point of the square
has zero circulation around its boundary. No derivative of the covector at
an interface, or countability of an exceptional set, is required. -/
theorem rectangle_integral_eq
    (B : Plane → Plane →L[ℝ] ℝ) (hB : ContinuousOn B square)
    (hlocal : ∀ z ∈ square, ∃ V : Set Plane,
      z ∈ V ∧ IsOpen V ∧ ∃ G : Plane → ℝ,
        ∀ w ∈ V, HasFDerivAt G (B w) w) :
    (∫ x in (0 : ℝ)..1, B (x,0) (1,0)) +
      (∫ y in (0 : ℝ)..1, B (1,y) (0,1)) =
    (∫ x in (0 : ℝ)..1, B (x,1) (1,0)) +
      (∫ y in (0 : ℝ)..1, B (0,y) (0,1)) := by
  classical
  let coeSquare : I × I → Plane := fun z => (z.1,z.2)
  have hcoe : Continuous coeSquare :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hex (z : I × I) : ∃ V : Set Plane,
      coeSquare z ∈ V ∧ IsOpen V ∧ ∃ G : Plane → ℝ,
        ∀ w ∈ V, HasFDerivAt G (B w) w :=
    hlocal (coeSquare z) ⟨z.1.2,z.2.2⟩
  choose V hmem hopen G hG using hex
  let cover : I × I → Set (I × I) := fun z => coeSquare ⁻¹' V z
  have hcoverOpen (z : I × I) : IsOpen (cover z) := (hopen z).preimage hcoe
  have hcover : univ ⊆ ⋃ z, cover z := by
    intro z _
    exact mem_iUnion.mpr ⟨z,hmem z⟩
  obtain ⟨t,ht0,htmono,⟨N,hN⟩,hgrid⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hcoverOpen hcover
  let a : ℕ → ℝ := fun i => t i
  have ha0 : a 0 = 0 := congrArg (fun x : I => (x : ℝ)) ht0
  have haN : a N = 1 := congrArg (fun x : I => (x : ℝ)) (hN N le_rfl)
  have hamono : Monotone a := fun i j hij => htmono hij
  have hrow (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun x => B (x,y) (1,0)) (Icc 0 1) := by
    exact (hB.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx,hy⟩)).eval_const (1,0)
  have hcol (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun y => B (x,y) (0,1)) (Icc 0 1) := by
    exact (hB.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => ⟨hx,hy⟩)).eval_const (0,1)
  have hinterval (i : ℕ) : Icc (a i) (a (i+1)) ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨(t i).2.1.trans hx.1,hx.2.trans (t (i+1)).2.2⟩
  have hrowInt (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) (i : ℕ) :
      IntervalIntegrable (fun x => B (x,y) (1,0)) volume (a i) (a (i+1)) :=
    ((hrow y hy).mono (hinterval i)).intervalIntegrable_of_Icc (hamono (Nat.le_succ i))
  have hcolInt (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (j : ℕ) :
      IntervalIntegrable (fun y => B (x,y) (0,1)) volume (a j) (a (j+1)) :=
    ((hcol x hx).mono (hinterval j)).intervalIntegrable_of_Icc (hamono (Nat.le_succ j))
  let H : ℕ → ℕ → ℝ := fun i j => ∫ x in a i..a (i+1), B (x,a j) (1,0)
  let W : ℕ → ℕ → ℝ := fun i j => ∫ y in a j..a (j+1), B (a i,y) (0,1)
  have hcell (i j : ℕ) : H i (j+1) - H i j = W (i+1) j - W i j := by
    obtain ⟨z,hz⟩ := hgrid i j
    have hsub : Icc (a i) (a (i+1)) ×ˢ Icc (a j) (a (j+1)) ⊆ V z := by
      rintro ⟨x,y⟩ ⟨hx,hy⟩
      let x' : I := ⟨x,hinterval i hx⟩
      let y' : I := ⟨y,hinterval j hy⟩
      exact hz (show (x',y') ∈ Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1)) from
        ⟨hx,hy⟩)
    have hhorizontal (y : ℝ) (hy : y ∈ Icc (a j) (a (j+1))) :
        (∫ x in a i..a (i+1), B (x,y) (1,0)) = G z (a (i+1),y) - G z (a i,y) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => G z (x,y))
        (f' := fun x : ℝ => B (x,y) (1,0))
      · intro x hx
        rw [uIcc_of_le (hamono (Nat.le_succ i))] at hx
        exact (hG z (x,y) (hsub ⟨hx,hy⟩)).comp_hasDerivAt x
          ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
      · exact hrowInt y (hinterval j hy) i
    have hvertical (x : ℝ) (hx : x ∈ Icc (a i) (a (i+1))) :
        (∫ y in a j..a (j+1), B (x,y) (0,1)) = G z (x,a (j+1)) - G z (x,a j) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => G z (x,y))
        (f' := fun y : ℝ => B (x,y) (0,1))
      · intro y hy
        rw [uIcc_of_le (hamono (Nat.le_succ j))] at hy
        exact (hG z (x,y) (hsub ⟨hx,hy⟩)).comp_hasDerivAt y
          ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
      · exact hcolInt x (hinterval i hx) j
    dsimp only [H,W]
    rw [hhorizontal _ ⟨hamono (Nat.le_succ j),le_rfl⟩,
      hhorizontal _ ⟨le_rfl,hamono (Nat.le_succ j)⟩,
      hvertical _ ⟨hamono (Nat.le_succ i),le_rfl⟩,
      hvertical _ ⟨le_rfl,hamono (Nat.le_succ i)⟩]
    ring
  let S : ℕ → ℝ := fun j => ∑ i ∈ Finset.range N, H i j
  have hstep (j : ℕ) : S (j+1) - S j = W N j - W 0 j := by
    calc
      S (j+1) - S j = ∑ i ∈ Finset.range N, (H i (j+1) - H i j) :=
        (Finset.sum_sub_distrib (fun i => H i (j+1)) (fun i => H i j)).symm
      _ = ∑ i ∈ Finset.range N, (W (i+1) j - W i j) :=
        Finset.sum_congr rfl (fun i _ => hcell i j)
      _ = W N j - W 0 j := Finset.sum_range_sub (fun i => W i j) N
  have htotal : S N - S 0 =
      (∑ j ∈ Finset.range N, W N j) - ∑ j ∈ Finset.range N, W 0 j := by
    calc
      S N - S 0 = ∑ j ∈ Finset.range N, (S (j+1) - S j) :=
        (Finset.sum_range_sub S N).symm
      _ = ∑ j ∈ Finset.range N, (W N j - W 0 j) :=
        Finset.sum_congr rfl (fun j _ => hstep j)
      _ = _ := Finset.sum_sub_distrib (fun j => W N j) (fun j => W 0 j)
  have hsumH (j : ℕ) : S j = ∫ x in (0 : ℝ)..1, B (x,a j) (1,0) := by
    dsimp only [S,H]
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun i _ => hrowInt (a j) (t j).2 i),ha0,haN]
  have hsumW (i : ℕ) : (∑ j ∈ Finset.range N, W i j) =
      ∫ y in (0 : ℝ)..1, B (a i,y) (0,1) := by
    dsimp only [W]
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => hcolInt (a i) (t i).2 j),ha0,haN]
  rw [hsumH,hsumH,hsumW,hsumW,ha0,haN] at htotal
  linarith

end CFMPLocalExactRectangle277Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPLocalExactRectangle277Transient.rectangle_integral_eq
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP277 local-exact finite-grid circulation absent: {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP277 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP277 CHECKED {name} axioms={axioms}"
