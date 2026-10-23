/- GID: D5/S3/Topology/Resolution/RelativeOpen
   generality: G
   mirror-B: D5/B/S3/Topology/Resolution/RelativeOpen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative metrizable kernels admit zero-dimensional open-preserving resolutions. -/

import D5.S3.Topology.Selection.CompactZeroDimensional
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.EquivFin

/-!
# Relative open-preserving resolutions

The base is compact Hausdorff and totally disconnected, without a metric
assumption. A compact metric coordinate separates the points within each fiber.
Finite global section nets and clopen distance bands give a closed path space.
Its uniform limit returns to the original compact Hausdorff domain.
-/

open Set Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace D5.S3.Topology.Resolution.RelativeOpen

universe uB uT uK uI

private theorem extend_prefix (I : ℕ → Type uI)
    (R : ∀ n, I n → I (n + 1) → Prop)
    (serial : ∀ n i, ∃ j, R n i j) (x : ∀ n, I n) (N : ℕ)
    (valid : ∀ n, n + 1 < N → R n (x n) (x (n + 1))) :
    ∃ a : ∀ n, I n, (∀ n, R n (a n) (a (n + 1))) ∧
      ∀ n, n < N → a n = x n := by
  classical
  let a : ∀ n, I n := fun n => Nat.rec (motive := fun n => I n) (x 0)
    (fun n i => if n + 1 < N then x (n + 1) else (serial n i).choose) n
  have az : a 0 = x 0 := rfl
  have asucc : ∀ n, a (n + 1) =
      if n + 1 < N then x (n + 1) else (serial n (a n)).choose := fun _ => rfl
  have agree : ∀ n, n < N → a n = x n := by
    intro n hn
    cases n with
    | zero => exact az
    | succ n => rw [asucc, if_pos hn]
  refine ⟨a, ?_, agree⟩
  intro n
  by_cases hn : n + 1 < N
  · rw [asucc, if_pos hn, agree n (by omega)]
    exact valid n hn
  · rw [asucc, if_neg hn]
    exact (serial n (a n)).choose_spec

section PathSpace

variable {B : Type uB} [TopologicalSpace B]
variable (I : ℕ → Type uI) [∀ n, TopologicalSpace (I n)]
  [∀ n, DiscreteTopology (I n)] [∀ n, Finite (I n)]
variable (A : ∀ n, I n → I (n + 1) → Set B)

private def paths : Set (B × (∀ n, I n)) :=
  {x | ∀ n, x.1 ∈ A n (x.2 n) (x.2 (n + 1))}

private theorem paths_closed (hA : ∀ n i j, IsClopen (A n i j)) :
    IsClosed (paths I A) := by
  have one : ∀ n, IsClosed {x : B × (∀ n, I n) |
      x.1 ∈ A n (x.2 n) (x.2 (n + 1))} := by
    intro n
    have eqslice : {x : B × (∀ n, I n) |
        x.1 ∈ A n (x.2 n) (x.2 (n + 1))} =
        ⋃ i : I n, ⋃ j : I (n + 1),
          (Prod.fst ⁻¹' A n i j) ∩
          ((fun x : B × (∀ n, I n) => x.2 n) ⁻¹' {i}) ∩
          ((fun x : B × (∀ n, I n) => x.2 (n + 1)) ⁻¹' {j}) := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage,
        mem_singleton_iff]
      constructor
      · intro h
        exact ⟨x.2 n, x.2 (n + 1), ⟨h, rfl⟩, rfl⟩
      · rintro ⟨i, j, ⟨h, hi⟩, hj⟩
        simpa [hi, hj] using h
    rw [eqslice]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro j
    exact (((hA n i j).isClosed.preimage continuous_fst).inter
      (isClosed_singleton.preimage ((continuous_apply n).comp continuous_snd))).inter
      (isClosed_singleton.preimage ((continuous_apply (n + 1)).comp continuous_snd))
  have eqall : paths I A = ⋂ n, {x : B × (∀ n, I n) |
      x.1 ∈ A n (x.2 n) (x.2 (n + 1))} := by ext x; simp [paths]
  rw [eqall]
  exact isClosed_iInter one

omit [TopologicalSpace B] [∀ n, DiscreteTopology (I n)] [∀ n, Finite (I n)] in
private theorem cylinder_image
    (serial : ∀ b n i, ∃ j, b ∈ A n i j)
    (V : Set B) (x : ∀ n, I n) (N : ℕ) :
    (fun z : paths I A => z.val.1) ''
        {z | z.val.1 ∈ V ∧ z.val.2 ∈ PiNat.cylinder x N} =
      V ∩ ⋂ n ∈ Finset.range (N - 1), A n (x n) (x (n + 1)) := by
  classical
  ext b
  simp only [mem_image, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨z, ⟨hzV, hprefix⟩, rfl⟩
    refine ⟨hzV, ?_⟩
    intro n hn
    have hlt := Finset.mem_range.mp hn
    have hnN : n < N := by omega
    have hsN : n + 1 < N := by omega
    have hp := z.property n
    rw [hprefix n hnN, hprefix (n + 1) hsN] at hp
    exact hp
  · rintro ⟨hbV, hb⟩
    by_cases hN : N = 0
    · subst N
      obtain ⟨a, ha, _⟩ := extend_prefix I (fun n i j => b ∈ A n i j)
        (serial b) x 0 (by intro n hn; omega)
      exact ⟨⟨(b, a), ha⟩, ⟨hbV, by simp⟩, rfl⟩
    have valid : ∀ n, n + 1 < N → b ∈ A n (x n) (x (n + 1)) := by
      intro n hn
      exact hb n (Finset.mem_range.mpr (by omega))
    obtain ⟨a, ha, heq⟩ := extend_prefix I (fun n i j => b ∈ A n i j)
      (serial b) x N valid
    refine ⟨⟨(b, a), ha⟩, ⟨hbV, ?_⟩, rfl⟩
    exact heq

omit [∀ n, Finite (I n)] in
private theorem paths_projection_open (hA : ∀ n i j, IsClopen (A n i j))
    (serial : ∀ b n i, ∃ j, b ∈ A n i j) :
    IsOpenMap (fun z : paths I A => z.val.1) := by
  let base : Set (Set B) := {V | IsOpen V}
  let cyl : Set (Set (∀ n, I n)) := {U | ∃ x N, U = PiNat.cylinder x N}
  have hbase : IsTopologicalBasis base := isTopologicalBasis_opens
  have hcyl : IsTopologicalBasis cyl := PiNat.isTopologicalBasis_cylinders I
  have hprod := hbase.prod hcyl
  have hsub := isTopologicalBasis_subtype hprod (fun x => x ∈ paths I A)
  apply hsub.isOpenMap_iff.mpr
  intro U hU
  rcases hU with ⟨W, hW, rfl⟩
  rcases hW with ⟨V, hV, C, hC, rfl⟩
  rcases hC with ⟨x, N, rfl⟩
  change IsOpen ((fun z : paths I A => z.val.1) ''
    {z | z.val.1 ∈ V ∧ z.val.2 ∈ PiNat.cylinder x N})
  rw [cylinder_image I A serial]
  exact hV.inter (isOpen_biInter_finset fun n _ => (hA n (x n) (x (n + 1))).isOpen)

end PathSpace

section Resolution

variable {B : Type uB} {T : Type uT} {K : Type uK}
  [TopologicalSpace B] [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B]
  [TopologicalSpace T] [CompactSpace T] [T2Space T]
  [MetricSpace K] [CompactSpace K]

omit [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B]
  [T2Space T] [CompactSpace K] in
private theorem finite_section_net (p : T → B) (u : T → K)
    (hp : Continuous p) (hu : Continuous u) (Phi : B → Set K)
    (through : ∀ t, ∃ v : B → K, Continuous v ∧
      (∀ b, v b ∈ Phi b) ∧ v (p t) = u t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ v : Fin N → B → K,
      (∀ i, Continuous (v i)) ∧ (∀ i b, v i b ∈ Phi b) ∧
      ∀ t, ∃ i, dist (u t) (v i (p t)) < ε := by
  classical
  choose v hv hmem heq using through
  let W : T → Set T := fun t => {x | dist (u x) (v t (p x)) < ε}
  have hopen : ∀ t, IsOpen (W t) := fun t =>
    isOpen_lt (hu.dist ((hv t).comp hp)) continuous_const
  have hcover : (univ : Set T) ⊆ ⋃ t, W t := by
    intro t _
    exact mem_iUnion.mpr ⟨t, by simpa [W, heq t] using hε⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover W hopen hcover
  let index : Fin s.card → s := s.equivFin.symm
  refine ⟨s.card, fun i => v (index i), fun i => hv _, fun i b => hmem _ b, ?_⟩
  intro t
  have ht := hs (mem_univ t)
  simp only [mem_iUnion] at ht
  obtain ⟨a, ha, ht⟩ := ht
  refine ⟨s.equivFin ⟨a, ha⟩, ?_⟩
  simpa [index, W] using ht

/-- Resolve an open compact map with a compact metrizable kernel, preserving
openness over the original, possibly nonmetrizable base. -/
theorem exists_relative_open_resolution (p : T → B) (u : T → K)
    (hp : Continuous p) (hpopen : IsOpenMap p) (hpon : Function.Surjective p)
    (hu : Continuous u) (he : IsEmbedding (fun t => (p t, u t))) :
    ∃ (Z : Type uB) (tZ : TopologicalSpace Z),
      let := tZ
      CompactSpace Z ∧ T2Space Z ∧ TotallyDisconnectedSpace Z ∧
      ∃ r : Z → T, Continuous r ∧ Function.Surjective r ∧
        IsOpenMap (p ∘ r) ∧ Function.Surjective (p ∘ r) ∧
        (MetrizableSpace B → MetrizableSpace Z) := by
  classical
  let : CompleteSpace K := complete_of_compact
  let F : Set (B × K) := range (fun t => (p t, u t))
  let Phi : B → Set K := fun b => {k | (b, k) ∈ F}
  have hF : IsClosed F := (hp.prodMk hu).isClosedMap.isClosed_range
  have hne : ∀ b, (Phi b).Nonempty := by
    intro b
    obtain ⟨t, ht⟩ := hpon b
    exact ⟨u t, ⟨t, by simp [ht]⟩⟩
  have hclosed : ∀ b, IsClosed (Phi b) := fun b =>
    hF.preimage (continuous_const.prodMk continuous_id)
  have hit : ∀ U : Set K,
      {b | (Phi b ∩ U).Nonempty} = p '' (u ⁻¹' U) := by
    intro U
    ext b
    constructor
    · rintro ⟨k, ⟨t, ht⟩, hkU⟩
      have hb : p t = b := congrArg Prod.fst ht
      have hk : u t = k := congrArg Prod.snd ht
      exact ⟨t, by simpa [hk] using hkU, hb⟩
    · rintro ⟨t, htU, rfl⟩
      exact ⟨u t, ⟨t, rfl⟩, htU⟩
  have hlsc : ∀ U : Set K, IsOpen U → IsOpen {b | (Phi b ∩ U).Nonempty} := by
    intro U hU
    rw [hit]
    exact hpopen _ (hU.preimage hu)
  have through : ∀ t, ∃ v : B → K, Continuous v ∧
      (∀ b, v b ∈ Phi b) ∧ v (p t) = u t := fun t =>
    Selection.CompactZeroDimensional.exists_continuous_selection_through
      Phi hne hclosed hlsc (p t) (u t) ⟨t, rfl⟩
  let eps : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have epspos : ∀ n, 0 < eps n := fun n => pow_pos (by norm_num) n
  have epssucc : ∀ n, eps (n + 1) = eps n / 2 := by
    intro n
    simp [eps, pow_succ, div_eq_mul_inv, mul_comm]
  choose N v hv hmember hnetT using
    (fun n => finite_section_net p u hp hu Phi through (eps n) (epspos n))
  let I : ℕ → Type := fun n => Fin (N n)
  let : ∀ n, TopologicalSpace (I n) := fun _ => ⊥
  let : ∀ n, DiscreteTopology (I n) := fun _ => ⟨rfl⟩
  have net : ∀ n b k, k ∈ Phi b → ∃ i : I n, dist k (v n i b) < eps n := by
    intro n b k hk
    obtain ⟨t, ht⟩ := hk
    obtain ⟨i, hi⟩ := hnetT n t
    have hb : p t = b := congrArg Prod.fst ht
    have hk' : u t = k := congrArg Prod.snd ht
    exact ⟨i, by simpa [hb, hk'] using hi⟩
  have bands : ∀ n (i : I n) (j : I (n + 1)), ∃ A : Set B,
      IsClopen A ∧
      {b | dist (v n i b) (v (n + 1) j b) ≤ eps n + eps (n + 1)} ⊆ A ∧
      A ⊆ {b | dist (v n i b) (v (n + 1) j b) < 2 * eps n + eps (n + 1)} := by
    intro n i j
    apply exists_clopen_of_closed_subset_open
      (isClosed_le ((hv n i).dist (hv (n + 1) j)) continuous_const)
      (isOpen_lt ((hv n i).dist (hv (n + 1) j)) continuous_const)
    intro b hb
    have hpos := epspos n
    change dist (v n i b) (v (n + 1) j b) ≤ _ at hb
    change dist (v n i b) (v (n + 1) j b) < _
    linarith
  choose A hA hlower hupper using bands
  have serial : ∀ b n (i : I n), ∃ j, b ∈ A n i j := by
    intro b n i
    obtain ⟨j, hj⟩ := net (n + 1) b (v n i b) (hmember n i b)
    exact ⟨j, hlower n i j (by change dist _ _ ≤ _; linarith [epspos n])⟩
  have target : ∀ b k, k ∈ Phi b → ∃ a : ∀ n, I n,
      (∀ n, b ∈ A n (a n) (a (n + 1))) ∧
      ∀ n, dist k (v n (a n) b) < eps n := by
    intro b k hk
    choose a ha using fun n => net n b k hk
    refine ⟨a, ?_, ha⟩
    intro n
    apply hlower n (a n) (a (n + 1))
    change dist _ _ ≤ _
    have ht := dist_triangle (v n (a n) b) k (v (n + 1) (a (n + 1)) b)
    rw [dist_comm (v n (a n) b) k] at ht
    linarith [ha n, ha (n + 1)]
  let Z := paths I A
  let : CompactSpace Z := isCompact_iff_compactSpace.mp
    ((paths_closed I A hA).isCompact)
  let q : Z → B := fun z => z.val.1
  have hq : Continuous q := continuous_fst.comp continuous_subtype_val
  have heval : ∀ n, Continuous (fun z : Z => v n (z.val.2 n) (q z)) := by
    intro n
    have h : Continuous (fun x : B × I n => v n x.2 x.1) :=
      continuous_prod_of_discrete_right.mpr (hv n)
    exact h.comp (hq.prodMk ((continuous_apply n).comp
      (continuous_snd.comp continuous_subtype_val)))
  let f : ℕ → Z →ᵇ K := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun z => v n (z.val.2 n) (q z), heval n⟩
  have step : ∀ n, dist (f n) (f (n + 1)) ≤ (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    apply (BoundedContinuousFunction.dist_le (by positivity)).mpr
    intro z
    have hb := hupper n (z.val.2 n) (z.val.2 (n + 1)) (z.property n)
    change dist (v n (z.val.2 n) (q z)) (v (n + 1) (z.val.2 (n + 1)) (q z)) ≤ _
    change dist (v n (z.val.2 n) (q z)) (v (n + 1) (z.val.2 (n + 1)) (q z)) < _ at hb
    rw [epssucc] at hb
    change _ ≤ (5 / 2 : ℝ) * eps n
    linarith
  have hcauchy : CauchySeq f := cauchySeq_of_le_geometric
    (1 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num) step
  obtain ⟨k, hk⟩ := cauchySeq_tendsto_of_complete hcauchy
  have tail : ∀ n, dist (f n) k ≤ 5 * eps n := by
    intro n
    have h := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) (5 / 2 : ℝ)
      (by norm_num : (1 / 2 : ℝ) < 1) step hk n
    convert h using 1
    dsimp [eps]
    ring
  have eval_limit : ∀ z : Z, Tendsto (fun n => f n z) atTop (𝓝 (k z)) := fun z =>
    ((BoundedContinuousFunction.lipschitz_eval_const z).continuous.tendsto k).comp hk
  have member_limit : ∀ z : Z, (q z, k z) ∈ F := by
    intro z
    apply hF.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds (eval_limit z))
    exact Eventually.of_forall (fun n => hmember n (z.val.2 n) (q z))
  let intoF : Z → F := fun z => ⟨(q z, k z), member_limit z⟩
  have hintoF : Continuous intoF := (hq.prodMk k.continuous).subtype_mk _
  let r : Z → T := fun z => he.toHomeomorph.symm (intoF z)
  have hr : Continuous r := he.toHomeomorph.symm.continuous.comp hintoF
  have eqbase : p ∘ r = q := by
    funext z
    have h := congrArg (fun y : F => y.val.1) (he.toHomeomorph.apply_symm_apply (intoF z))
    change p (r z) = q z at h
    exact h
  have ronto : Function.Surjective r := by
    intro t
    obtain ⟨a, ha, happrox⟩ := target (p t) (u t) ⟨t, rfl⟩
    let z : Z := ⟨(p t, a), ha⟩
    have bound : ∀ n, dist (k z) (u t) ≤ 6 * eps n := by
      intro n
      have ht : dist (k z) (f n z) ≤ 5 * eps n := by
        rw [dist_comm]
        exact (BoundedContinuousFunction.dist_coe_le_dist z).trans (tail n)
      have ha' : dist (f n z) (u t) < eps n := by
        simpa only [f, z, q, BoundedContinuousFunction.mkOfCompact_apply,
          ContinuousMap.coe_mk, dist_comm] using happrox n
      linarith [dist_triangle (k z) (f n z) (u t)]
    have hd : dist (k z) (u t) ≤ 0 := le_of_tendsto_of_tendsto'
      tendsto_const_nhds
      (by simpa [eps] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 6) bound
    have hkt : k z = u t := dist_le_zero.mp hd
    refine ⟨z, ?_⟩
    have hint : intoF z = ⟨(p t, u t), ⟨t, rfl⟩⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hkt
    change he.toHomeomorph.symm (intoF z) = t
    rw [hint]
    exact he.toHomeomorph_symm_apply t
  have qopen : IsOpenMap q := paths_projection_open I A hA serial
  have metric : MetrizableSpace B → MetrizableSpace Z := by
    intro hB
    let : MetrizableSpace B := hB
    let : MetricSpace (∀ n, I n) := PiNat.metricSpace
    infer_instance
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance,
    r, hr, ronto, ?_, ?_, metric⟩
  · rw [eqbase]
    exact qopen
  · exact hpon.comp ronto

end Resolution

end D5.S3.Topology.Resolution.RelativeOpen
