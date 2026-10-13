/- GID: D5/S3/Topology/Resolution/OpenPullbackObstruction
   generality: G
   mirror-B: D5/B/S3/Topology/Resolution/OpenPullbackObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Topology/Resolution/OpenPullbackObstruction.claim; result=D5/S3/Topology/Resolution/OpenPullbackObstruction.result; claim=D5/S3/Topology/Resolution/OpenPullbackObstruction.claim
   digest: Preselected zero-dimensional resolutions fail full-pullback openness. -/

import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Set.Card

/-!
# Obstruction to preselected full-pullback compatibility

The base is binary Cantor space with its product topology. The interval is
literally the usual closed real unit interval. The resolution domain can have
arbitrary weight. A later two-to-one extension makes its full pullback nonopen.
This concerns preselection and the entire pullback, not adaptive resolutions.
-/

open Set Filter Topology TopologicalSpace
open scoped unitInterval

namespace D5.S3.Topology.Resolution.OpenPullbackObstruction

abbrev Cantor := ℕ → Bool
abbrev Square := Cantor × I
abbrev Extension := Square ⊕ Cantor

def star : Cantor := fun _ => false

private theorem cylinder_clopen (n : ℕ) : IsClopen (PiNat.cylinder star n) := by
  refine ⟨?_, PiNat.isOpen_cylinder _ _ _⟩
  rw [PiNat.cylinder_eq_pi]
  exact isClosed_set_pi fun _ _ => isClosed_singleton

private theorem cylinder_neighborhood {U : Set Cantor} (hU : IsOpen U) (hstar : star ∈ U) :
    ∃ n, PiNat.cylinder star n ⊆ U := by
  obtain ⟨_, ⟨b, n, rfl⟩, hb, hsub⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => Bool)).exists_subset_of_mem_open hstar hU
  refine ⟨n, ?_⟩
  rwa [← PiNat.mem_cylinder_iff_eq.mp hb] at hsub

/-- A convergent interval sequence is realized on shrinking Cantor annuli.
The chosen point in each annulus can simultaneously lie in a prescribed
neighborhood of the all-false point. -/
private theorem annular_section (x : ℕ → I) (c : I)
    (hx : Tendsto x atTop (𝓝 c)) (U : ℕ → Set Cantor)
    (hU : ∀ n, IsOpen (U n)) (hstar : ∀ n, star ∈ U n) :
    ∃ s : Cantor → I, Continuous s ∧ s star = c ∧
      ∃ b : ℕ → Cantor, Tendsto b atTop (𝓝 star) ∧
        ∀ n, b n ∈ U n ∧ s (b n) = x n := by
  classical
  choose m hm using fun n => cylinder_neighborhood (hU n) (hstar n)
  let k : ℕ → ℕ := fun n => Nat.rec 0 (fun n v => max v (m n) + 1) n
  have k0 : k 0 = 0 := rfl
  have ks : ∀ n, k (n + 1) = max (k n) (m n) + 1 := fun _ => rfl
  have klt : ∀ n, k n < k (n + 1) := by
    intro n
    rw [ks]
    omega
  have kmono : StrictMono k := strictMono_nat_of_lt_succ klt
  have kn : ∀ n, n ≤ k n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := klt n; omega
  let V : ℕ → Set Cantor := fun n => PiNat.cylinder star (k n)
  have Vanti : Antitone V := fun _ _ hij => PiNat.cylinder_anti _ (kmono.monotone hij)
  have Vstar : ∀ n, star ∈ V n := fun n => PiNat.self_mem_cylinder _ _
  have escape : ∀ b : Cantor, b ≠ star → ∃ n, b ∉ V (n + 1) := by
    intro b hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
    refine ⟨i, ?_⟩
    intro h
    exact hi (PiNat.mem_cylinder_iff.mp h i (by have := kn (i + 1); omega))
  let rank : Cantor → ℕ := fun b => if h : b ≠ star then Nat.find (escape b h) else 0
  have rank_out : ∀ b, b ≠ star → b ∉ V (rank b + 1) := by
    intro b hb
    dsimp [rank]
    rw [dif_pos hb]
    exact Nat.find_spec (escape b hb)
  have rank_in : ∀ b, b ≠ star → b ∈ V (rank b) := by
    intro b hb
    dsimp [rank]
    rw [dif_pos hb]
    generalize heq : Nat.find (escape b hb) = n
    cases n with
    | zero => simp [V, k0, PiNat.cylinder_zero]
    | succ n =>
      have h := Nat.find_min (escape b hb) (show n < Nat.find (escape b hb) by omega)
      exact not_not.mp h
  have rank_eq : ∀ b n, b ∈ V n → b ∉ V (n + 1) → b ≠ star ∧ rank b = n := by
    intro b n hin hout
    have hb : b ≠ star := fun he => hout (he ▸ Vstar (n + 1))
    refine ⟨hb, le_antisymm ?_ ?_⟩
    · dsimp [rank]
      rw [dif_pos hb]
      exact Nat.find_min' (escape b hb) hout
    · by_contra h
      have hle : rank b + 1 ≤ n := by omega
      exact rank_out b hb (Vanti hle hin)
  let s : Cantor → I := fun b => if b = star then c else x (rank b)
  have sstar : s star = c := by simp [s]
  have sann : ∀ b n, b ∈ V n → b ∉ V (n + 1) → s b = x n := by
    intro b n hi ho
    obtain ⟨hb, hr⟩ := rank_eq b n hi ho
    simp [s, hb, hr]
  have hs : Continuous s := by
    apply continuous_iff_continuousAt.mpr
    intro b
    by_cases hb : b = star
    · subst b
      rw [ContinuousAt, sstar]
      apply tendsto_def.mpr
      intro W hW
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hx hW)
      have hc : c ∈ W := mem_of_mem_nhds hW
      filter_upwards [(cylinder_clopen (k N)).isOpen.mem_nhds (Vstar N)] with b hbin
      by_cases hb : b = star
      · simpa [hb, sstar] using hc
      · have hNr : N ≤ rank b := by
          by_contra h
          have hle : rank b + 1 ≤ N := by omega
          exact rank_out b hb (Vanti hle hbin)
        simpa [s, hb] using hN (rank b) hNr
    · have ha : IsOpen (V (rank b) \ V (rank b + 1)) :=
        (cylinder_clopen _).isOpen.sdiff (cylinder_clopen _).isClosed
      have hmem : b ∈ V (rank b) \ V (rank b + 1) := ⟨rank_in b hb, rank_out b hb⟩
      apply ContinuousAt.congr_of_eventuallyEq (continuousAt_const (y := x (rank b)))
      filter_upwards [ha.mem_nhds hmem] with d hd
      exact sann d (rank b) hd.1 hd.2
  let b : ℕ → Cantor := fun n => Function.update star (max (k n) (m n)) true
  have bV : ∀ n, b n ∈ V n := by
    intro n i hi
    dsimp [b]
    rw [Function.update_of_ne (show i ≠ max (k n) (m n) by omega)]
  have bnot : ∀ n, b n ∉ V (n + 1) := by
    intro n h
    have hh := h (max (k n) (m n)) (by rw [ks]; omega)
    simp [b, star] at hh
  have bU : ∀ n, b n ∈ U n := by
    intro n
    apply hm n
    intro i hi
    dsimp [b]
    rw [Function.update_of_ne (show i ≠ max (k n) (m n) by omega)]
  have blim : Tendsto b atTop (𝓝 star) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_def.mpr
    intro W hW
    have hf : false ∈ W := mem_of_mem_nhds hW
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    have hi : i ≠ max (k n) (m n) := by have := kn n; omega
    simpa [b, Function.update_of_ne hi, star] using hf
  exact ⟨s, hs, sstar, b, blim, fun n => ⟨bU n, sann _ _ (bV n) (bnot n)⟩⟩


/-- A closed subset of the Cantor square which contains the lower endpoint
and misses the upper endpoint on one vertical fiber has a continuous section
whose incidence set is closed but not open. -/
theorem exists_nonopen_section (K : Set Square) (hK : IsClosed K)
    (hzero : (star, (0 : I)) ∈ K) (hone : (star, (1 : I)) ∉ K) :
    ∃ s : Cantor → I, Continuous s ∧
      IsClosed {b | (b, s b) ∈ K} ∧ ¬ IsOpen {b | (b, s b) ∈ K} := by
  classical
  let L : Set I := {x | (star, x) ∈ K}
  have hL : IsClosed L := hK.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨c, hc, hmax⟩ := hL.isCompact.exists_isGreatest ⟨0, hzero⟩
  have hc1 : (c : ℝ) < 1 := by
    have hne : c ≠ 1 := fun he => hone (he ▸ hc)
    exact lt_of_le_of_ne c.property.2 (by simpa using hne)
  let x : ℕ → I := fun n =>
    ⟨(c : ℝ) + (1 - c) / ((n : ℝ) + 2), by
      have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      constructor
      · exact add_nonneg c.property.1 (div_nonneg (by linarith) hd.le)
      · have hf : (1 - (c : ℝ)) / ((n : ℝ) + 2) ≤ 1 - c := by
          apply (div_le_iff₀ hd).mpr
          have hn : (0 : ℝ) ≤ n := by positivity
          nlinarith
        linarith⟩
  have xc : ∀ n, c < x n := by
    intro n
    change (c : ℝ) < (c : ℝ) + (1 - c) / ((n : ℝ) + 2)
    exact lt_add_of_pos_right _ (div_pos (by linarith) (by positivity))
  have xout : ∀ n, (star, x n) ∉ K := fun n hn => (not_le.mpr (xc n)) (hmax hn)
  have xlim : Tendsto x atTop (𝓝 c) := by
    apply tendsto_subtype_rng.mpr
    have ht : Tendsto (fun n : ℕ => (1 - (c : ℝ)) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_add_atTop_iff_nat 2).mpr (tendsto_const_div_atTop_nhds_zero_nat (1 - (c : ℝ)))
    simpa only [x, add_zero] using tendsto_const_nhds.add ht
  let U : ℕ → Set Cantor := fun n => {b | (b, x n) ∉ K}
  have hU : ∀ n, IsOpen (U n) := fun n =>
    hK.isOpen_compl.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨s, hs, hsc, b, hblim, hb⟩ := annular_section x c xlim U hU xout
  have hD : IsClosed {b | (b, s b) ∈ K} := hK.preimage (continuous_id.prodMk hs)
  refine ⟨s, hs, hD, ?_⟩
  intro hopen
  have hmem : star ∈ {b | (b, s b) ∈ K} := by
    change (star, s star) ∈ K
    rw [hsc]
    exact hc
  have hev : ∀ᶠ n in atTop, (b n, s (b n)) ∈ K := hblim (hopen.mem_nhds hmem)
  obtain ⟨n, hn⟩ := hev.exists
  have hbn := (hb n).1
  exact hbn (by simpa only [(hb n).2] using hn)


/-- Forget the binary label: the left summand is the whole square and the
right summand is the graph of the constructed section. -/
def forget (s : Cantor → I) : Extension → Square := Sum.elim id (fun b => (b, s b))

def base : Extension → Cantor := Sum.elim Prod.fst id

def binary (s : Cantor → I) : Extension → Square × Bool :=
  Sum.elim (fun z => (z, false)) (fun b => ((b, s b), true))

def binarySet (s : Cantor → I) : Set (Square × Bool) :=
  {z | z.2 = false ∨ (z.2 = true ∧ z.1.2 = s z.1.1)}

/-- The literal full pullback, with the induced product-subtype topology. -/
abbrev Pullback {E : Type*} (a : E → Square) (s : Cantor → I) :=
  {te : Extension × E // forget s te.1 = a te.2}

def toExtension {E : Type*} (a : E → Square) (s : Cantor → I) : Pullback a s → Extension :=
  fun z => z.val.1

def toResolution {E : Type*} (a : E → Square) (s : Cantor → I) : Pullback a s → E :=
  fun z => z.val.2

def rho {E : Type*} (a : E → Square) (s : Cantor → I) : Pullback a s → Cantor :=
  base ∘ toExtension a s

/-- The extra graph label retains exactly these resolution points. -/
def sectionFiber {E : Type*} (a : E → Square) (s : Cantor → I) : Set E :=
  {e | a e = ((a e).1, s (a e).1)}

private theorem forget_continuous {s : Cantor → I} (hs : Continuous s) : Continuous (forget s) :=
  continuous_id.sumElim (continuous_id.prodMk hs)

private theorem binary_embedding {s : Cantor → I} (hs : Continuous s) :
    IsClosedEmbedding (binary s) ∧ Set.range (binary s) = binarySet s := by
  have hc : Continuous (binary s) :=
    (continuous_id.prodMk continuous_const).sumElim
      ((continuous_id.prodMk hs).prodMk continuous_const)
  have hi : Function.Injective (binary s) := by
    intro t u h
    cases t with
    | inl z =>
      cases u with
      | inl w => exact congrArg Sum.inl (congrArg Prod.fst h)
      | inr b => have hh := congrArg Prod.snd h; cases hh
    | inr b =>
      cases u with
      | inl z => have hh := congrArg Prod.snd h; cases hh
      | inr d => exact congrArg Sum.inr (congrArg (fun z : Square × Bool => z.1.1) h)
  refine ⟨hc.isClosedEmbedding hi, ?_⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    cases t <;> simp [binary, binarySet]
  · rintro (h | ⟨h, hx⟩)
    · refine ⟨Sum.inl z.1, ?_⟩
      exact Prod.ext rfl h.symm
    · refine ⟨Sum.inr z.1.1, ?_⟩
      exact Prod.ext (Prod.ext rfl hx.symm) h.symm

private theorem forget_fiber_bound (s : Cantor → I) (z : Square) :
    {t | forget s t = z}.encard ≤ 2 := by
  have hsub : {t | forget s t = z} ⊆ {Sum.inl z, Sum.inr z.1} := by
    intro t ht
    cases t with
    | inl w => exact Or.inl (congrArg Sum.inl ht)
    | inr b => exact Or.inr (congrArg Sum.inr (congrArg Prod.fst ht))
  exact (Set.encard_mono hsub).trans_eq (Set.encard_pair (by simp))

private theorem sectionFiber_closed {E : Type*} [TopologicalSpace E]
    {a : E → Square} (ha : Continuous a) {s : Cantor → I} (hs : Continuous s) :
    IsClosed (sectionFiber a s) :=
  isClosed_eq ha ((continuous_fst.comp ha).prodMk (hs.comp (continuous_fst.comp ha)))

private def sumToPullback {E : Type*} (a : E → Square) (s : Cantor → I) :
    E ⊕ sectionFiber a s → Pullback a s :=
  Sum.elim (fun e => ⟨(Sum.inl (a e), e), rfl⟩)
    (fun z => ⟨(Sum.inr (a z.val).1, z.val), z.property.symm⟩)

private theorem pullback_homeomorph {E : Type*} [TopologicalSpace E]
    [CompactSpace E] [T2Space E] {a : E → Square} (ha : Continuous a)
    {s : Cantor → I} (hs : Continuous s) :
    ∃ e : (E ⊕ sectionFiber a s) ≃ₜ Pullback a s,
      ∀ z, e z = sumToPullback a s z := by
  let : CompactSpace (sectionFiber a s) :=
    isCompact_iff_compactSpace.mp (sectionFiber_closed ha hs).isCompact
  have hc : Continuous (sumToPullback a s) :=
    ((continuous_inl.comp ha).prodMk continuous_id).subtype_mk _ |>.sumElim
      (((continuous_inr.comp (continuous_fst.comp (ha.comp continuous_subtype_val))).prodMk
        continuous_subtype_val).subtype_mk _)
  have hi : Function.Injective (sumToPullback a s) := by
    intro z w h
    cases z with
    | inl e =>
      cases w with
      | inl d => exact congrArg Sum.inl (congrArg (fun z => z.val.2) h)
      | inr d => have hh := congrArg (fun z => z.val.1) h; cases hh
    | inr e =>
      cases w with
      | inl d => have hh := congrArg (fun z => z.val.1) h; cases hh
      | inr d => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z => z.val.2) h))
  have ho : Function.Surjective (sumToPullback a s) := by
    rintro ⟨⟨t, e⟩, ht⟩
    cases t with
    | inl z =>
      refine ⟨Sum.inl e, Subtype.ext ?_⟩
      exact Prod.ext (congrArg Sum.inl ht.symm) rfl
    | inr b =>
      have he : a e = (b, s b) := ht.symm
      have hb : (a e).1 = b := congrArg Prod.fst he
      have hf : e ∈ sectionFiber a s := by
        change a e = ((a e).1, s (a e).1)
        rw [hb]
        exact he
      refine ⟨Sum.inr ⟨e, hf⟩, Subtype.ext ?_⟩
      exact Prod.ext (congrArg Sum.inr hb) rfl
  let e := hc.isClosedEmbedding hi |>.isEmbedding.toHomeomorphOfSurjective ho
  exact ⟨e, fun _ => rfl⟩


universe u v

/-- The complete certificate refers to the literal full pullback, its two
standard projections, and the actual binary-coordinate embedding. -/
structure Construction {E : Type u} [TopologicalSpace E]
    (a : E → Square) (s : Cantor → I) : Prop where
  sectionContinuous : Continuous s
  extensionCompact : CompactSpace Extension
  extensionMetrizable : MetrizableSpace Extension
  baseContinuous : Continuous base
  baseOpen : IsOpenMap base
  baseSurjective : Function.Surjective base
  forgetContinuous : Continuous (forget s)
  forgetSurjective : Function.Surjective (forget s)
  overBase : Prod.fst ∘ forget s = base
  fibersAtMostTwo : ∀ z, {t | forget s t = z}.encard ≤ 2
  binaryEmbedding : IsClosedEmbedding (binary s)
  binaryRange : Set.range (binary s) = binarySet s
  binaryClosed : IsClosed (binarySet s)
  binaryForgetting : ∀ t, (binary s t).1 = forget s t
  sectionFiberClosed : IsClosed (sectionFiber a s)
  pullbackCompact : CompactSpace (Pullback a s)
  pullbackHausdorff : T2Space (Pullback a s)
  pullbackZeroDimensional : TotallyDisconnectedSpace (Pullback a s)
  pullbackClopenBasis : IsTopologicalBasis {U : Set (Pullback a s) | IsClopen U}
  toExtensionContinuous : Continuous (toExtension a s)
  toResolutionContinuous : Continuous (toResolution a s)
  toExtensionSurjective : Function.Surjective (toExtension a s)
  toResolutionSurjective : Function.Surjective (toResolution a s)
  commonComposite : rho a s = Prod.fst ∘ a ∘ toResolution a s
  compositeContinuous : Continuous (rho a s)
  compositeNotOpen : ¬ IsOpenMap (rho a s)
  noRepair : ∀ (Y : Type v) [TopologicalSpace Y] (h : Y → Pullback a s),
    Continuous h → Function.Surjective h → ¬ IsOpenMap (rho a s ∘ h)
  pullbackModel : ∃ e : (E ⊕ sectionFiber a s) ≃ₜ Pullback a s,
    ∀ z, e z = sumToPullback a s z

/-- Every preselected arbitrary-weight resolution is defeated by a later
surjective extension with at most two points in each forgetting fiber.
No initial openness hypothesis on the resolution is used. -/
theorem exists_obstruction {E : Type u} [TopologicalSpace E]
    [CompactSpace E] [T2Space E] [TotallyDisconnectedSpace E]
    (a : E → Square) (ha : Continuous a) (hao : Function.Surjective a) :
    ∃ s : Cantor → I, Construction.{u, v} a s := by
  classical
  let A0 : Set E := a ⁻¹' {(star, (0 : I))}
  let A1 : Set E := a ⁻¹' {(star, (1 : I))}
  have hA0 : IsClosed A0 := isClosed_singleton.preimage ha
  have hA1 : IsClosed A1 := isClosed_singleton.preimage ha
  have hdis : A0 ⊆ A1ᶜ := by
    intro e he0 he1
    have h : (0 : I) = 1 := congrArg Prod.snd (he0.symm.trans he1)
    exact zero_ne_one h
  obtain ⟨H, hH, h0H, hH1⟩ := exists_clopen_of_closed_subset_open hA0 hA1.isOpen_compl hdis
  let K : Set Square := a '' H
  have hK : IsClosed K := (hH.isClosed.isCompact.image ha).isClosed
  have hzero : (star, (0 : I)) ∈ K := by
    obtain ⟨e, he⟩ := hao (star, 0)
    exact ⟨e, h0H he, he⟩
  have hone : (star, (1 : I)) ∉ K := by
    rintro ⟨e, heH, he⟩
    exact hH1 heH he
  obtain ⟨s, hs, _, hD⟩ := exists_nonopen_section K hK hzero hone
  have hcT : CompactSpace Extension := inferInstance
  have hcF : IsClosed (sectionFiber a s) := sectionFiber_closed ha hs
  let : CompactSpace (sectionFiber a s) := isCompact_iff_compactSpace.mp hcF.isCompact
  obtain ⟨equiv, hequiv⟩ := pullback_homeomorph ha hs
  have hcP : CompactSpace (Pullback a s) := equiv.compactSpace
  have hdP : TotallyDisconnectedSpace (Pullback a s) := equiv.totallyDisconnectedSpace
  have hte : Continuous (toExtension a s) := continuous_fst.comp continuous_subtype_val
  have hea : Continuous (toResolution a s) := continuous_snd.comp continuous_subtype_val
  have hbase : Continuous base := continuous_fst.sumElim continuous_id
  have hcom : rho a s = Prod.fst ∘ a ∘ toResolution a s := by
    funext z
    have h := congrArg Prod.fst z.property
    cases ht : z.val.1 <;> simpa [rho, toExtension, toResolution, base, forget, ht] using h
  let G : Set (Pullback a s) :=
    (toResolution a s ⁻¹' H) ∩ (toExtension a s ⁻¹' Set.range Sum.inr)
  have hG : IsClopen G := (hH.preimage hea).inter (isClopen_range_inr.preimage hte)
  have imageG : rho a s '' G = {b | (b, s b) ∈ K} := by
    ext b
    constructor
    · rintro ⟨z, ⟨hzH, hzR⟩, hzb⟩
      obtain ⟨d, hd⟩ := hzR
      change Sum.inr d = z.val.1 at hd
      have hf : (d, s d) = a z.val.2 := by
        have hz := z.property
        rw [← hd] at hz
        exact hz
      have hdb : d = b := by
        change base z.val.1 = b at hzb
        rw [← hd] at hzb
        exact hzb
      change (b, s b) ∈ a '' H
      exact ⟨z.val.2, hzH, hdb ▸ hf.symm⟩
    · rintro ⟨e, heH, he⟩
      let z : Pullback a s := ⟨(Sum.inr b, e), he.symm⟩
      exact ⟨z, ⟨heH, ⟨b, rfl⟩⟩, rfl⟩
  have hnonopen : ¬ IsOpenMap (rho a s) := by
    intro ho
    exact hD (imageG ▸ ho G hG.isOpen)
  obtain ⟨hbembed, hbrange⟩ := binary_embedding hs
  have hmetric : MetrizableSpace Extension := by
    let : MetricSpace Cantor := PiNat.metricSpace
    exact hbembed.isEmbedding.metrizableSpace
  refine ⟨s, { sectionContinuous := hs
               extensionCompact := hcT
               extensionMetrizable := hmetric
               baseContinuous := hbase
               baseOpen := isOpenMap_fst.sumElim IsOpenMap.id
               baseSurjective := ?_
               forgetContinuous := forget_continuous hs
               forgetSurjective := fun z => ⟨Sum.inl z, rfl⟩
               overBase := ?_
               fibersAtMostTwo := forget_fiber_bound s
               binaryEmbedding := hbembed
               binaryRange := hbrange
               binaryClosed := hbrange ▸ hbembed.isClosed_range
               binaryForgetting := ?_
               sectionFiberClosed := hcF
               pullbackCompact := hcP
               pullbackHausdorff := inferInstance
               pullbackZeroDimensional := hdP
               pullbackClopenBasis := by
                 let := hcP
                 let := hdP
                 exact isTopologicalBasis_isClopen
               toExtensionContinuous := hte
               toResolutionContinuous := hea
               toExtensionSurjective := ?_
               toResolutionSurjective := ?_
               commonComposite := hcom
               compositeContinuous := hbase.comp hte
               compositeNotOpen := hnonopen
               noRepair := fun Y _ h hh hho ho => hnonopen (IsOpenMap.of_comp hh hho ho)
               pullbackModel := ⟨equiv, hequiv⟩ }⟩
  · intro b
    exact ⟨Sum.inr b, rfl⟩
  · funext t
    cases t <;> rfl
  · intro t
    cases t <;> rfl
  · intro t
    obtain ⟨e, he⟩ := hao (forget s t)
    exact ⟨⟨(t, e), he.symm⟩, rfl⟩
  · intro e
    exact ⟨⟨(Sum.inl (a e), e), rfl⟩, rfl⟩


/-- Generic literal full pullback used to state the preselection claim. -/
abbrev FullPullback {T E : Type*} (f : T → Square) (a : E → Square) :=
  {te : T × E // f te.1 = a te.2}

def fullComposite {T E : Type*} (f : T → Square) (a : E → Square) :
    FullPullback f a → Cantor := fun te => (f te.val.1).1

/-- A single initially open preselected resolution is required to preserve
openness under every later compact metrizable surjective binary-coordinate
extension with forgetting fibers of cardinality at most two. -/
def claim : Prop :=
  ∃ (E : Type) (tE : TopologicalSpace E) (_ : @CompactSpace E tE)
    (_ : @T2Space E tE) (_ : @TotallyDisconnectedSpace E tE),
    let := tE
    ∃ a : E → Square, Continuous a ∧ Function.Surjective a ∧
      IsOpenMap (Prod.fst ∘ a) ∧
      ∀ (T : Type) (tT : TopologicalSpace T) (_ : @CompactSpace T tT)
        (_ : @MetrizableSpace T tT),
        letI := tT
        ∀ f : T → Square, Continuous f → Function.Surjective f →
          IsOpenMap (Prod.fst ∘ f) → Function.Surjective (Prod.fst ∘ f) →
          (∀ z, {t | f t = z}.encard ≤ 2) →
          (∃ j : T → Bool, Continuous j ∧ IsClosedEmbedding (fun t => (f t, j t))) →
          IsOpenMap (fullComposite f a)

/-- No preselected resolution has the universal full-pullback stability
property, even when it is initially open and later coordinates are binary. -/
theorem result : ¬ claim := by
  rintro ⟨E, tE, hcE, hhE, hdE, a, ha, hao, _, hstable⟩
  let := tE
  let := hcE
  let := hhE
  let := hdE
  obtain ⟨s, hs⟩ := exists_obstruction.{0, 0} a ha hao
  have hover : Prod.fst ∘ forget s = base := hs.overBase
  have hj : ∃ j : Extension → Bool, Continuous j ∧
      IsClosedEmbedding (fun t => (forget s t, j t)) := by
    let j : Extension → Bool := Sum.elim (fun _ => false) (fun _ => true)
    have heq : (fun t => (forget s t, j t)) = binary s := by
      funext t
      cases t <;> rfl
    exact ⟨j, continuous_const.sumElim continuous_const, heq ▸ hs.binaryEmbedding⟩
  have ho := hstable Extension inferInstance hs.extensionCompact hs.extensionMetrizable
    (forget s) hs.forgetContinuous hs.forgetSurjective
    (hover ▸ hs.baseOpen) (hover ▸ hs.baseSurjective) hs.fibersAtMostTwo hj
  have heq : fullComposite (forget s) a = rho a s := by
    funext te
    exact congrFun hover te.val.1
  exact hs.compositeNotOpen (heq ▸ ho)

end D5.S3.Topology.Resolution.OpenPullbackObstruction
