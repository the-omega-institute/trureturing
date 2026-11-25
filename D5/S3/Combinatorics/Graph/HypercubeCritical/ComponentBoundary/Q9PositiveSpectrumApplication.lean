/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Actual Q9 occupied components have adjacency eigenvalue four and eight-star rigidity. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositivePairedKernel
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.DiamondFreeSpectral
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarRigidity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairedFibreAnyAxis

/-! The positive kernel on an actual paired-fibre component has adjacency
eigenvalue four. Its smallest possible support is an eight-column star. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositiveSpectrumApplication

open scoped BigOperators Matrix
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCriticalSpectrum (Q flip_adj IsSwitching IsBalanced
  switching_sq directionEdges direction_edge_count)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions flip_injective)
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows emptyFibreBoundary)
open Q9PositivePairedKernel (pairedVertex pairedGraph dropAxis occupiedContact
  occupiedContact_iff_projected_adj occupied occupiedMatrix emptyMatrix vertex_injective
  occupied_entry occupied_entry_zero split_gram empty_boundary_iff switch_twice)
open Q9EightStarRigidity (SwitchingCoherent switchedEntry occupiedAxes mem_occupiedAxes
  occupied_common_row_unique occupied_edge_triangle_unique occupiedK44_star)
open PrimeContactCubeOrders (rowContacts mem_rowContacts)
open PrimeContactCardinalityGap (commonIn mem_commonIn)
open HuangBalancedSymmetry (cube_action_regular_balanced)
open Q9OccupiedFibreParity (doubleFibres)
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private liftVertex flip_insert insert_drop drop_insert parity_flip doubleFibres_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
open private axisToZero mem_image_cons_iff mem_paired mem_single opposite_parity
  firstAxisSingleFibres no_adjacent_pairs paired_column coherent_entry from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairedFibreAnyAxis
open private flip_cons_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private reindex reindex_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

attribute [local instance] Classical.propDecidable

variable {C : Finset (Q 9)} {b : Bool} {i : Fin 9}
variable {k : (pairedGraph C b i).ConnectedComponent}

/-- The paired columns in one occupied connected component. -/
abbrev ComponentRows (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (k : (pairedGraph C b i).ConnectedComponent) :=
  {x : PairedRows C b i // (pairedGraph C b i).connectedComponentMk x = k}

/-- Projection of that component, using the order-preserving deletion of the axis. -/
def componentColumns (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (k : (pairedGraph C b i).ConnectedComponent) : Finset (Q 8) :=
  univ.image (fun x : ComponentRows C b i k => dropAxis i (pairedVertex x.1))

/-- Actual occupied status of a projected fibre. -/
def projectedOccupied (C : Finset (Q 9)) (i : Fin 9) (r : Q 8) : Bool :=
  decide (liftVertex i false r ∈ C ∨ liftVertex i true r ∈ C)

private abbrev project (x : ComponentRows C b i k) : Q 8 :=
  dropAxis i (pairedVertex x.1)

private theorem occupied_iff_projected (r : Q 9) :
    occupied C i r ↔ projectedOccupied C i (dropAxis i r) = true := by
  have h₀ : liftVertex i (r i) (dropAxis i r) = r := insert_drop i r
  have h₁ : flip r i = liftVertex i (!(r i)) (dropAxis i r) := by
    rw [← flip_insert, h₀]
  unfold occupied projectedOccupied
  rw [decide_eq_true_eq]
  cases h : r i
  · rw [h] at h₀ h₁
    simp only [Bool.not_false] at h₁
    have hp : r ∈ C ↔ liftVertex i false (dropAxis i r) ∈ C := by rw [h₀]
    have hp' : flip r i ∈ C ↔ liftVertex i true (dropAxis i r) ∈ C := by rw [← h₁]
    exact or_congr hp hp'
  · rw [h] at h₀ h₁
    simp only [Bool.not_true] at h₁
    have hp : r ∈ C ↔ liftVertex i true (dropAxis i r) ∈ C := by rw [h₀]
    have hp' : flip r i ∈ C ↔ liftVertex i false (dropAxis i r) ∈ C := by rw [← h₁]
    exact (or_congr hp hp').trans or_comm

private theorem projected_pair (x : PairedRows C b i) (t : Bool) :
    liftVertex i t (dropAxis i (pairedVertex x)) ∈ C := by
  let v := pairedVertex x
  have hv : v ∈ C := x.1.1.property
  have hv' : flip v i ∈ C := x.property
  have he : liftVertex i (v i) (dropAxis i v) = v := insert_drop i v
  have he' : liftVertex i (!(v i)) (dropAxis i v) = flip v i := by
    rw [← flip_insert, he]
  have hm : liftVertex i (v i) (dropAxis i v) ∈ C := by rw [he]; exact hv
  have hm' : liftVertex i (!(v i)) (dropAxis i v) ∈ C := by rw [he']; exact hv'
  cases ht : v i <;> cases t
  · simpa only [ht] using hm
  · simpa only [ht, Bool.not_false] using hm'
  · simpa only [ht, Bool.not_true] using hm'
  · simpa only [ht] using hm

private theorem same_layer_of_adj {x y : PairedRows C b i}
    (hxy : (pairedGraph C b i).Adj x y) :
    pairedVertex x i = pairedVertex y i := by
  obtain ⟨_, r, hx, hy⟩ := hxy
  exact ((occupiedContact_iff_projected_adj r x).mp hx).2.1.symm.trans
    ((occupiedContact_iff_projected_adj r y).mp hy).2.1

private theorem same_layer (x y : ComponentRows C b i k) :
    pairedVertex x.1 i = pairedVertex y.1 i := by
  have along {a d : PairedRows C b i} (h : (pairedGraph C b i).Reachable a d) :
      pairedVertex a i = pairedVertex d i := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => rfl
    | cons h _ ih => exact (same_layer_of_adj h).trans ih
  exact along (SimpleGraph.ConnectedComponent.exact (x.property.trans y.property.symm))

private theorem project_injective :
    Function.Injective (project (C := C) (b := b) (i := i) (k := k)) := by
  intro x y h
  apply Subtype.ext
  apply vertex_injective
  calc
    pairedVertex x.1 = liftVertex i (pairedVertex x.1 i) (project x) :=
      (insert_drop i _).symm
    _ = liftVertex i (pairedVertex y.1 i) (project y) := by rw [same_layer x y, h]
    _ = pairedVertex y.1 := insert_drop i _

private theorem mem_columns (q : Q 8) :
    q ∈ componentColumns C b i k ↔ ∃ x : ComponentRows C b i k, project x = q := by
  simp only [componentColumns, mem_image, mem_univ, true_and]

private theorem card_columns :
    (componentColumns C b i k).card = Fintype.card (ComponentRows C b i k) := by
  rw [componentColumns, card_image_of_injective _ project_injective, card_univ]

private theorem column_pair {q : Q 8} (hq : q ∈ componentColumns C b i k) (t : Bool) :
    liftVertex i t q ∈ C := by
  obtain ⟨x, rfl⟩ := (mem_columns q).mp hq
  exact projected_pair x.1 t

private theorem contact_of_projected {x : PairedRows C b i} {r : Q 8}
    (ho : projectedOccupied C i r = true) (ha : (hypercube 8).Adj r (dropAxis i (pairedVertex x))) :
    occupiedContact C b i (liftVertex i (pairedVertex x i) r) x := by
  let s := liftVertex i (pairedVertex x i) r
  have hd : dropAxis i s = r := drop_insert i _ _
  refine (occupiedContact_iff_projected_adj s x).mpr ⟨?_, ?_, ?_⟩
  · change occupied C i s
    exact (occupied_iff_projected s).mpr (hd.symm ▸ ho)
  · exact Fin.insertNth_apply_same (α := fun _ => Bool) i _ _
  · rw [hd]
    exact ha

abbrev componentGraph (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (k : (pairedGraph C b i).ConnectedComponent) : SimpleGraph (ComponentRows C b i k) :=
  (pairedGraph C b i).induce {x | (pairedGraph C b i).connectedComponentMk x = k}

private theorem component_adj_iff (x y : ComponentRows C b i k) :
    (componentGraph C b i k).Adj x y ↔
      (Q9EightStarRigidity.occupiedGraph (componentColumns C b i k)
        (projectedOccupied C i)).Adj (project x) (project y) := by
  constructor
  · rintro ⟨hne, r, hx, hy⟩
    obtain ⟨hor, _, hrx⟩ := (occupiedContact_iff_projected_adj r x.1).mp hx
    obtain ⟨_, _, hry⟩ := (occupiedContact_iff_projected_adj r y.1).mp hy
    exact ⟨(mem_columns _).mpr ⟨x, rfl⟩, (mem_columns _).mpr ⟨y, rfl⟩,
      fun he => hne (congrArg Subtype.val (project_injective he)), dropAxis i r,
      (occupied_iff_projected r).mp hor, hrx.symm, hry.symm⟩
  · rintro ⟨_, _, hne, r, ho, hrx, hry⟩
    refine ⟨fun he => hne (congrArg (fun z => dropAxis i (pairedVertex z)) he),
      liftVertex i (pairedVertex x.1 i) r, contact_of_projected ho hrx.symm, ?_⟩
    rw [same_layer x y]
    exact contact_of_projected ho hry.symm

/-- The actual projected column set satisfies switching coherence, the
three-contact cap and the four-occupied-directions identity. Axis
normalization is used only for these unweighted geometric facts. -/
private theorem projected_geometry
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ τ : Q 8 → ℝ,
      SwitchingCoherent (componentColumns C b i k) (projectedOccupied C i) τ ∧
      (∀ r, projectedOccupied C i r = true →
        (rowContacts (componentColumns C b i k) r).card ≤ 3) ∧
      (∀ q ∈ componentColumns C b i k, (occupiedAxes (projectedOccupied C i) q).card = 4) := by
  let K := componentColumns C b i k
  let D := C.image (reindex (axisToZero i))
  obtain ⟨hrD, hbD⟩ := cube_action_regular_balanced (reindex (axisToZero i))
    (axisToZero i) (reindex_flip (axisToZero i)) hr hb
  obtain ⟨s, hs⟩ := hbD
  have hpair {q : Q 8} (hq : q ∈ K) (t : Bool) : Fin.cons t q ∈ D :=
    (mem_image_cons_iff C i t q).mpr (column_pair hq t)
  have hocc (r : Q 8) : projectedOccupied C i r = true ↔
      Fin.cons false r ∈ D ∨ Fin.cons true r ∈ D := by
    simp only [projectedOccupied, decide_eq_true_eq, D, mem_image_cons_iff]
  have hentry {q r : Q 8} (hq : q ∈ K) (ha : (hypercube 8).Adj q r)
      {t : Bool} (ht : Fin.cons t r ∈ D) :
      switchedEntry (fun x => s (Fin.cons false x)) r q =
        (if t then 1 else -1) * s (Fin.cons t r) := by
    obtain ⟨j, rfl⟩ := adjacent_exists_flip ha.symm
    exact coherent_entry hs ht j (hpair hq false) (hpair hq true)
  refine ⟨fun q => s (Fin.cons false q), ⟨fun q hq => switching_sq hs (hpair hq false), ?_⟩,
    ?_, ?_⟩
  · intro q p r hq hp hqr hpr hor
    obtain ⟨t, ht⟩ : ∃ t : Bool, Fin.cons t r ∈ D := by
      rcases (hocc r).mp hor with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    exact (hentry hq hqr ht).trans (hentry hp hpr ht).symm
  · intro r hor
    obtain ⟨t, ht⟩ : ∃ t : Bool, Fin.cons t r ∈ D := by
      rcases (hocc r).mp hor with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have hparams (q : Q 8) (hq : q ∈ rowContacts K r) :
        ∃ j : Fin 9, j ∈ directions D (Fin.cons t r) ∧
          Fin.cons t q = flip (Fin.cons t r) j := by
      obtain ⟨hqK, ha⟩ := mem_rowContacts.mp hq
      obtain ⟨j, rfl⟩ := adjacent_exists_flip ha.symm
      refine ⟨j.succ, (mem_directions D _ _).mpr ?_, ?_⟩
      · rw [flip_cons_succ]
        exact hpair hqK t
      · rw [flip_cons_succ]
    choose j hj he using hparams
    rw [← regular_directions D hrD ht]
    exact card_le_card_of_injOn (fun q => if h : q ∈ rowContacts K r then j q h else 0)
      (by intro q hq; change q ∈ rowContacts K r at hq; simpa only [dite_eq_left hq, Finset.mem_coe] using hj q hq)
      (by
        intro q hq p hp heq
        change q ∈ rowContacts K r at hq
        change p ∈ rowContacts K r at hp
        simp only [dif_pos hq, dif_pos hp] at heq
        simpa only [Fin.tail_cons] using congrArg (Fin.tail (α := fun _ => Bool))
          ((he q hq).trans ((congrArg (flip (Fin.cons t r)) heq).trans (he p hp).symm)))
  · intro q hq
    let p := cubeParity q
    have hqP : q ∈ doubleFibres D 0 p := mem_paired.mpr ⟨⟨hpair hq false, hpair hq true⟩, rfl⟩
    have he : occupiedAxes (projectedOccupied C i) q =
        directions (firstAxisSingleFibres D (!p)) q := by
      ext j
      rw [mem_occupiedAxes, hocc, mem_directions, mem_single,
        opposite_parity q j p rfl]
      have hn := no_adjacent_pairs ⟨s, hs⟩ (hpair hq false) (hpair hq true) j
      simp only [eq_self, true_and] <;> tauto
    rw [he]
    exact paired_column hrD ⟨s, hs⟩ hqP

private theorem occupied_cap {τ : Q 8 → ℝ}
    (hs : SwitchingCoherent (componentColumns C b i k) (projectedOccupied C i) τ)
    (hcap : ∀ r, projectedOccupied C i r = true →
      (rowContacts (componentColumns C b i k) r).card ≤ 3) :
    DiamondFreeSpectral.EdgeCommonCap (componentGraph C b i k) := by
  let G := componentGraph C b i k
  intro a b hab
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨_, hax, hbx⟩ := (mem_commonIn G).mp hx
  obtain ⟨_, hay, hby⟩ := (mem_commonIn G).mp hy
  exact project_injective (occupied_edge_triangle_unique hs hcap
    ((component_adj_iff a b).mp hab) ((component_adj_iff a x).mp hax)
    ((component_adj_iff b x).mp hbx) ((component_adj_iff a y).mp hay)
    ((component_adj_iff b y).mp hby))

private theorem contact_card (x : ComponentRows C b i k)
    (hfour : (occupiedAxes (projectedOccupied C i) (project x)).card = 4) :
    (univ.filter (fun r : Q 9 => occupiedContact C b i r x.1)).card = 4 := by
  rw [← hfour]
  symm
  apply card_bij (fun j _ => liftVertex i (pairedVertex x.1 i) (flip (project x) j))
  · intro j hj
    exact mem_filter.mpr ⟨mem_univ _, contact_of_projected
      (mem_occupiedAxes.mp hj) (flip_adj _ _).symm⟩
  · intro j _ l _ he
    apply flip_injective (project x)
    simpa only [Q9PositivePairedKernel.dropAxis, liftVertex, Fin.removeNth_insertNth] using congrArg (dropAxis i) he
  · intro r hr
    obtain ⟨ho, hb, ha⟩ := (occupiedContact_iff_projected_adj r x.1).mp (mem_filter.mp hr).2
    obtain ⟨j, hj⟩ := adjacent_exists_flip ha.symm
    refine ⟨j, mem_occupiedAxes.mpr (hj ▸ (occupied_iff_projected r).mp ho), ?_⟩
    rw [← hj, ← hb]
    exact insert_drop i r

private theorem contact_unique {τ : Q 8 → ℝ}
    (hs : SwitchingCoherent (componentColumns C b i k) (projectedOccupied C i) τ)
    {x y : ComponentRows C b i k} (hne : x ≠ y) {r s : Q 9}
    (hrx : occupiedContact C b i r x.1) (hry : occupiedContact C b i r y.1)
    (hsx : occupiedContact C b i s x.1) (hsy : occupiedContact C b i s y.1) :
    r = s := by
  obtain ⟨hro, hrbit, hrx'⟩ := (occupiedContact_iff_projected_adj r x.1).mp hrx
  obtain ⟨_, _, hry'⟩ := (occupiedContact_iff_projected_adj r y.1).mp hry
  obtain ⟨hso, hsbit, hsx'⟩ := (occupiedContact_iff_projected_adj s x.1).mp hsx
  obtain ⟨_, _, hsy'⟩ := (occupiedContact_iff_projected_adj s y.1).mp hsy
  have hd := occupied_common_row_unique hs
    ((mem_columns _).mpr ⟨x, rfl⟩) ((mem_columns _).mpr ⟨y, rfl⟩)
    (fun he => hne (project_injective he)) ((occupied_iff_projected r).mp hro)
    ((occupied_iff_projected s).mp hso) hrx'.symm hry'.symm hsx'.symm hsy'.symm
  calc
    r = liftVertex i (r i) (dropAxis i r) := (insert_drop i r).symm
    _ = liftVertex i (s i) (dropAxis i s) := by rw [hrbit, hsbit, hd]
    _ = s := insert_drop i s

private theorem occupied_unit_entry {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    (r : Q 9) (x : PairedRows C b i) :
    occupiedMatrix C b i σ (fun _ => 1) r x =
      if occupiedContact C b i r x then 1 else 0 := by
  by_cases h : occupiedContact C b i r x
  · rw [if_pos h]
    obtain ⟨ho, a, ha, he⟩ := h
    exact occupied_entry hs (fun _ => 1) ho ha he
  · rw [if_neg h]
    exact occupied_entry_zero σ (fun _ => 1) h

private theorem occupied_unit_gram {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {τ : Q 8 → ℝ}
    (ht : SwitchingCoherent (componentColumns C b i k) (projectedOccupied C i) τ)
    (hfour : ∀ q ∈ componentColumns C b i k, (occupiedAxes (projectedOccupied C i) q).card = 4)
    (x y : ComponentRows C b i k) :
    ((occupiedMatrix C b i σ (fun _ => 1))ᵀ *
      occupiedMatrix C b i σ (fun _ => 1)) x.1 y.1 =
      (if x = y then 4 else 0) + (componentGraph C b i k).adjMatrix ℝ x y := by
  let O := occupiedMatrix C b i σ (fun _ => 1)
  have he : (Oᵀ * O) x.1 y.1 =
      ((univ.filter (fun r : Q 9 => occupiedContact C b i r x.1 ∧
        occupiedContact C b i r y.1)).card : ℝ) := by
    simp only [O, Matrix.mul_apply, Matrix.transpose_apply, occupied_unit_entry hs,
      Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hx : occupiedContact C b i r x.1 <;>
      by_cases hy : occupiedContact C b i r y.1 <;> simp [hx, hy]
  rw [he]
  by_cases hxy : x = y
  · subst y
    have hc := contact_card x (hfour _ ((mem_columns _).mpr ⟨x, rfl⟩))
    simp only [and_self, hc, Nat.cast_ofNat, ite_true, SimpleGraph.adjMatrix_apply,
      SimpleGraph.irrefl, ite_false, add_zero]
  · rw [if_neg hxy, zero_add, SimpleGraph.adjMatrix_apply]
    by_cases ha : (componentGraph C b i k).Adj x y
    · obtain ⟨_, r, hrx, hry⟩ := ha
      have ha' : (componentGraph C b i k).Adj x y := ⟨fun he => hxy (Subtype.ext he), r, hrx, hry⟩
      have hset : (univ.filter (fun s : Q 9 => occupiedContact C b i s x.1 ∧
          occupiedContact C b i s y.1)) = {r} := by
        ext s
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun h => contact_unique ht hxy h.1 h.2 hrx hry,
          fun h => h.symm ▸ And.intro hrx hry⟩
      rw [if_pos ha', hset, card_singleton, Nat.cast_one]
    · have hz : (univ.filter (fun r : Q 9 => occupiedContact C b i r x.1 ∧
          occupiedContact C b i r y.1)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hrx, hry⟩ := (mem_filter.mp hr).2
        exact ha ⟨fun he => hxy (Subtype.ext he), r, hrx, hry⟩
      rw [if_neg ha, hz, card_empty, Nat.cast_zero]

/-- At unit transverse weights the occupied adjacency operator on the
kernel-carrying component has eigenvalue four. -/
theorem component_adjacency_eigenvalue
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {f : PairedRows C b i → ℝ}
    (hf : emptyFibreBoundary C b i (fun _ => 1) *ᵥ f = 0)
    (hzero : ∀ x, (pairedGraph C b i).connectedComponentMk x ≠ k → f x = 0) :
    ∀ x : ComponentRows C b i k,
      ((componentGraph C b i k).adjMatrix ℝ *ᵥ
        (fun y : ComponentRows C b i k => σ (pairedVertex y.1) * f y.1)) x =
        4 * (σ (pairedVertex x.1) * f x.1) := by
  obtain ⟨τ, ht, _, hfour⟩ := projected_geometry (k := k) hr ⟨σ, hs⟩
  let O := occupiedMatrix C b i σ (fun _ => 1)
  let E := emptyMatrix C b i σ (fun _ => 1)
  let u : PairedRows C b i → ℝ := fun x => σ (pairedVertex x) * f x
  have huE : E *ᵥ u = 0 := (empty_boundary_iff σ (fun _ => 1) u).mpr (by
    rw [show (fun x => σ (pairedVertex x) * u x) = f from switch_twice hs f]
    exact hf)
  have hc : (∑ a : Fin 9, (if a = i then (0 : ℝ) else 1) ^ 2) = 8 := by
    rw [← Finset.sum_erase_add univ _ (mem_univ i)]
    simp only [ite_true, zero_pow (by decide : 2 ≠ 0), add_zero]
    calc
      (∑ a ∈ (univ : Finset (Fin 9)).erase i, (if a = i then (0 : ℝ) else 1) ^ 2) =
          ∑ _a ∈ (univ : Finset (Fin 9)).erase i, (1 : ℝ) := by
        apply sum_congr rfl
        intro a ha
        rw [if_neg (mem_erase.mp ha).1, one_pow]
      _ = 8 := by simp
  have hGram : Oᵀ * O + Eᵀ * E = (8 : ℝ) • (1 : Matrix (PairedRows C b i) _ ℝ) := by
    have h := split_gram (b := b) (i := i) hs (fun _ => 1)
    rw [hc] at h
    exact h
  have hEigen := congrArg (fun M : Matrix (PairedRows C b i) (PairedRows C b i) ℝ => M *ᵥ u) hGram
  have heE : (Eᵀ * E) *ᵥ u = 0 := by
    rw [← Matrix.mulVec_mulVec, huE, Matrix.mulVec_zero]
  rw [Matrix.add_mulVec, heE, add_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec] at hEigen
  intro x
  have hrow : (∑ y : PairedRows C b i, (Oᵀ * O) x.1 y * u y) = 8 * u x.1 :=
    by simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using congrFun hEigen x.1
  have hrestrict :
      (∑ y : ComponentRows C b i k, (Oᵀ * O) x.1 y.1 * u y.1) =
        ∑ y : PairedRows C b i, (Oᵀ * O) x.1 y * u y := by
    refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ ?_
    · intro y hy
      have hn : (pairedGraph C b i).connectedComponentMk y ≠ k :=
        fun h => hy ⟨⟨y, h⟩, rfl⟩
      simp [u, hzero y hn]
    · intro y
      rfl
  rw [← hrestrict] at hrow
  have hsplit :
      (∑ y : ComponentRows C b i k, (Oᵀ * O) x.1 y.1 * u y.1) =
        4 * u x.1 + ((componentGraph C b i k).adjMatrix ℝ *ᵥ
          (fun y : ComponentRows C b i k => u y.1)) x := by
    calc
      _ = ∑ y : ComponentRows C b i k,
          ((if x = y then 4 else 0) * u y.1 +
            (componentGraph C b i k).adjMatrix ℝ x y * u y.1) := by
        apply sum_congr rfl
        intro y _
        rw [occupied_unit_gram hs ht hfour x y, add_mul]
      _ = _ := by
        have hd : (∑ y : ComponentRows C b i k, (if x = y then (4 : ℝ) else 0) * u y.1) =
            4 * u x.1 := by
          rw [sum_eq_single x]
          · simp
          · intro y _ hy
            rw [if_neg hy.symm, zero_mul]
          · simp
        rw [sum_add_distrib, hd] <;> rfl
  rw [hsplit] at hrow
  change ((componentGraph C b i k).adjMatrix ℝ *ᵥ
    (fun y : ComponentRows C b i k => u y.1)) x = 4 * u x.1
  linarith

/-- The component cardinal is at most the actual count of paired fibres
on the axis. Each projected column is mapped to the false endpoint once. -/
theorem component_card_le_paired_fibres :
    Fintype.card (ComponentRows C b i k) ≤ directionEdges C i := by
  let F := C.filter (fun x => x i = false ∧ BalancedCriticalSpectrum.flip x i ∈ C)
  let emb (x : ComponentRows C b i k) : F :=
    ⟨liftVertex i false (project x), mem_filter.mpr ⟨projected_pair x.1 false,
      Fin.insertNth_apply_same (α := fun _ => Bool) i false _,
      by rw [flip_insert, Bool.not_false]; exact projected_pair x.1 true⟩⟩
  have hinj : Function.Injective emb := by
    intro x y h
    apply project_injective
    simpa only [emb, Q9PositivePairedKernel.dropAxis, liftVertex, Fin.removeNth_insertNth] using congrArg (fun z : F => dropAxis i z.1) h
  simpa only [F, Fintype.card_coe, directionEdges] using Fintype.card_le_of_injective emb hinj

/-- A positive full-component kernel has at least eight projected columns.
In the equality case they are the eight neighbors of a unique empty fibre,
with an exact four-four partition determining the occupied mixed corners. -/
theorem positive_component_eight_star
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {f : PairedRows C b i → ℝ} (hfne : f ≠ 0)
    (hf : emptyFibreBoundary C b i (fun _ => 1) *ᵥ f = 0)
    (hzero : ∀ x, (pairedGraph C b i).connectedComponentMk x ≠ k → f x = 0)
    (hpos : ∀ x, (pairedGraph C b i).connectedComponentMk x = k → 0 < σ (pairedVertex x) * f x) :
    8 ≤ (componentColumns C b i k).card ∧ 8 ≤ directionEdges C i ∧
      ((componentColumns C b i k).card = 8 →
        ∃ A B : Finset (Q 8), A.card = 4 ∧ B.card = 4 ∧ Disjoint A B ∧
          A ∪ B = componentColumns C b i k ∧
          ∃! r : Q 8, projectedOccupied C i r = false ∧
            (∀ x, x ∈ componentColumns C b i k ↔ (hypercube 8).Adj r x) ∧
            (∀ j l : Fin 8, j ≠ l →
              (projectedOccupied C i (flip (flip r j) l) = true ↔
                (flip r j ∈ A ∧ flip r l ∈ B) ∨ (flip r j ∈ B ∧ flip r l ∈ A)))) := by
  let V := ComponentRows C b i k
  let G := componentGraph C b i k
  let p : V → Q 8 := project
  let K := componentColumns C b i k
  haveI : Nonempty V := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hfne
    have hxk : (pairedGraph C b i).connectedComponentMk x = k := by
      by_contra hn
      exact hx (hzero x hn)
    exact ⟨⟨x, hxk⟩⟩
  obtain ⟨τ, ht, hcap, hfour⟩ := projected_geometry (k := k) hr ⟨σ, hs⟩
  let u : V → ℝ := fun x => σ (pairedVertex x.1) * f x.1
  have he := component_adjacency_eigenvalue hr hs hf hzero
  obtain ⟨h8, hrigid⟩ := DiamondFreeSpectral.card_ge_eight_and_rigidity G
    (occupied_cap ht hcap) u (fun x => hpos x.1 x.property) he
  refine ⟨by rw [card_columns]; exact h8,
    h8.trans (component_card_le_paired_fibres (k := k)), ?_⟩
  intro hK
  obtain ⟨A₀, hA₀, hB₀, hpart₀⟩ := hrigid ((card_columns (k := k)).symm.trans hK)
  let A := A₀.image p
  let B := A₀ᶜ.image p
  have hp_inj : Function.Injective p := project_injective
  have hA : A.card = 4 := by
    change (A₀.image p).card = 4
    rw [card_image_of_injective _ hp_inj, hA₀]
  have hB : B.card = 4 := by
    change (A₀ᶜ.image p).card = 4
    rw [card_image_of_injective _ hp_inj, hB₀]
  have hmemA (x : V) : project x ∈ A ↔ x ∈ A₀ :=
    ⟨fun hx => by
      obtain ⟨y, hy, he⟩ := mem_image.mp hx
      exact (project_injective he) ▸ hy,
      fun hx => mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hmemB (x : V) : project x ∈ B ↔ x ∉ A₀ :=
    ⟨fun hx => by
      obtain ⟨y, hy, he⟩ := mem_image.mp hx
      have hxy : y = x := project_injective he
      exact mem_compl.mp (hxy ▸ hy),
      fun hx => mem_image.mpr ⟨x, mem_compl.mpr hx, rfl⟩⟩
  have hsep : Disjoint A B := Finset.disjoint_left.mpr (by
    intro q hqA hqB
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hqA
    exact (hmemB x).mp hqB hx)
  have hUnion : A ∪ B = K := by
    dsimp only [A, B, K, componentColumns, p]
    rw [← image_union, union_compl]
  have hpart (q r : Q 8) :
      (Q9EightStarRigidity.occupiedGraph (A ∪ B) (projectedOccupied C i)).Adj q r ↔
        (q ∈ A ∧ r ∈ B) ∨ (q ∈ B ∧ r ∈ A) := by
    rw [hUnion]
    constructor
    · intro hadj
      obtain ⟨x, rfl⟩ := (mem_columns q).mp hadj.1
      obtain ⟨y, rfl⟩ := (mem_columns r).mp hadj.2.1
      have h := (hpart₀ x y).mp ((component_adj_iff x y).mpr hadj)
      simpa only [hmemA, hmemB] using h
    · intro h
      have hq : q ∈ K := hUnion ▸ (mem_union.mpr (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)))
      have hr' : r ∈ K := hUnion ▸ (mem_union.mpr (h.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)))
      obtain ⟨x, rfl⟩ := (mem_columns q).mp hq
      obtain ⟨y, rfl⟩ := (mem_columns r).mp hr'
      exact (component_adj_iff x y).mp ((hpart₀ x y).mpr (by simpa only [hmemA, hmemB] using h))
  refine ⟨A, B, hA, hB, hsep, hUnion, ?_⟩
  have ht' : SwitchingCoherent (A ∪ B) (projectedOccupied C i) τ := hUnion.symm ▸ ht
  have hf' : ∀ q ∈ A ∪ B, (occupiedAxes (projectedOccupied C i) q).card = 4 := hUnion.symm ▸ hfour
  simpa only [hUnion] using occupiedK44_star ht' hA hB hsep hpart hf'

/-- Eight paired fibres in total would have to be the eight-star, all of
one projected parity. The exact occupied-fibre identity rules this out
by divisibility by three. -/
theorem positive_component_axis_ge_nine
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {f : PairedRows C b i → ℝ} (hfne : f ≠ 0)
    (hf : emptyFibreBoundary C b i (fun _ => 1) *ᵥ f = 0)
    (hzero : ∀ x, (pairedGraph C b i).connectedComponentMk x ≠ k → f x = 0)
    (hpos : ∀ x, (pairedGraph C b i).connectedComponentMk x = k → 0 < σ (pairedVertex x) * f x) :
    9 ≤ directionEdges C i := by
  obtain ⟨hc, hm, hstar⟩ := positive_component_eight_star (k := k) hr hs hfne hf hzero hpos
  by_contra hn
  have hm8 : directionEdges C i = 8 := by omega
  have hle := component_card_le_paired_fibres (C := C) (b := b) (i := i) (k := k)
  rw [← card_columns, hm8] at hle
  have hc8 : (componentColumns C b i k).card = 8 := by omega
  obtain ⟨_, _, _, _, _, _, r, ⟨_, hfull, _⟩, _⟩ := hstar hc8
  let p := !cubeParity r
  have hsub : componentColumns C b i k ⊆ doubleFibres C i p := by
    intro q hq
    have hqp : cubeParity q = p := by
      obtain ⟨a, rfl⟩ := adjacent_exists_flip ((hfull q).mp hq)
      exact parity_flip r a
    simp only [doubleFibres, mem_filter, mem_univ, true_and]
    exact ⟨⟨column_pair hq false, column_pair hq true⟩, hqp⟩
  have h8p := card_le_card hsub
  rw [hc8] at h8p
  have hpartition := doubleFibres_partition C i p
  have hidentity := Q9OccupiedFibreParity.occupied_fibre_identity hr ⟨σ, hs⟩ i p
  omega

open Q9ComponentSaturation (componentDefect exists_two_weighted_singular_components)
open TwoBalancedComponents (componentFinset)
open CoordinateHalves.Q9DominantAxisBoundary (exists_emptyFibreBoundary_kernel)
open Q9PositivePairedKernel (exists_fixed_occupiedComponent_emptyFibre_kernel)
open Translation.Q9ActualAperiodicity (signed_defect_det_eq_component)
open private regular_and_balanced_of_component_singular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open private gram_det_eq_zero_iff boundary_gram_eq_signed_defect from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary

/-- In an actual 258-vertex subcubic support, both weighted singular
components have at least nine paired fibres on every axis. On each axis
they have a fixed occupied component carrying all the weighted kernels,
with at least eight columns and eight-star rigidity at equality. -/
theorem exists_two_components_with_positive_spectrum_bound
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ A B : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      A ≠ B ∧ ∀ K, K = A ∨ K = B →
        let C := componentFinset U K
        ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
        ∃ σ : Q 9 → ℝ, IsSwitching C σ ∧ ∀ i : Fin 9,
          9 ≤ directionEdges C i ∧
          ∃ k : (pairedGraph C false i).ConnectedComponent,
            8 ≤ (componentColumns C false i k).card ∧
            (∀ w : Fin 9 → ℝ,
              ∃ f : PairedRows C false i → ℝ,
                f ≠ 0 ∧ emptyFibreBoundary C false i w *ᵥ f = 0 ∧
                (∀ x, (pairedGraph C false i).connectedComponentMk x ≠ k → f x = 0) ∧
                ((∀ a, a ≠ i → 0 < w a) →
                  ∀ x, (pairedGraph C false i).connectedComponentMk x = k →
                    0 < σ (pairedVertex x) * f x)) ∧
            ((componentColumns C false i k).card = 8 →
              ∃ P R : Finset (Q 8), P.card = 4 ∧ R.card = 4 ∧ Disjoint P R ∧
                P ∪ R = componentColumns C false i k ∧
                ∃! t : Q 8, projectedOccupied C i t = false ∧
                  (∀ x, x ∈ componentColumns C false i k ↔ (hypercube 8).Adj t x) ∧
                  (∀ j l : Fin 8, j ≠ l →
                    (projectedOccupied C i (flip (flip t j) l) = true ↔
                      (flip t j ∈ P ∧ flip t l ∈ R) ∨ (flip t j ∈ R ∧ flip t l ∈ P)))) := by
  obtain ⟨A, B, hAB, hdet⟩ := exists_two_weighted_singular_components U hU hdeg false
  refine ⟨A, B, hAB, fun K hK => ?_⟩
  have hKdet (w : Fin 9 → ℝ) : (componentDefect w U false K).det = 0 := by
    rcases hK with rfl | rfl
    · exact (hdet w).1
    · exact (hdet w).2
  obtain ⟨hr, ⟨σ, hs⟩⟩ := regular_and_balanced_of_component_singular U K hdeg
    (hKdet fun _ => 1)
  refine ⟨hr, σ, hs, fun i => ?_⟩
  obtain ⟨k, hk⟩ := exists_fixed_occupiedComponent_emptyFibre_kernel (b := false) (i := i) hs
    (fun w => by
      apply exists_emptyFibreBoundary_kernel (componentFinset U K) false _ i w
      intro v
      apply (gram_det_eq_zero_iff _).mp
      rw [boundary_gram_eq_signed_defect, signed_defect_det_eq_component]
      exact hKdet v)
  obtain ⟨f, hfne, hf, hzero, hpos⟩ := hk (fun _ => 1)
  have hp := hpos (fun _ _ => by norm_num)
  obtain ⟨h8, _, hstar⟩ := positive_component_eight_star hr hs hfne hf hzero hp
  exact ⟨positive_component_axis_ge_nine hr hs hfne hf hzero hp, k, h8, hk, hstar⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositiveSpectrumApplication
