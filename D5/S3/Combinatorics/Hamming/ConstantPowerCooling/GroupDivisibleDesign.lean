/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite group divisible designs attain the cooling-code leave bound. -/

import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.FiniteBound

/-! # Cooling codes from uniform group divisible designs -/

open scoped BigOperators
open Finset SimpleGraph

namespace CPECCBridge

/-- The equivalence classes of the setoid are the groups. A distinct within-group pair occurs
in no block, and a cross-group pair occurs in exactly one block. -/
structure GroupDivisibleDesign (V : Type*) [DecidableEq V] (k g : ℕ) where
  groups : Setoid V
  group_card : ∀ v, ({u | groups.r v u} : Set V).ncard = g
  blocks : Finset (Finset V)
  block_card : ∀ B ∈ blocks, B.card = k
  within_group : ∀ B ∈ blocks, ∀ ⦃u v⦄, u ∈ B → v ∈ B → u ≠ v → ¬ groups.r u v
  cross_group : ∀ ⦃u v⦄, ¬ groups.r u v → ∃! B, B ∈ blocks ∧ u ∈ B ∧ v ∈ B

/-- A family of information classes in the support model for correction radius $w-2$. -/
def IsSupportFamily {V I : Type*} [DecidableEq V]
    (P : I → Finset (Finset V)) (w t : ℕ) : Prop :=
  (∀ i A, A ∈ P i → A.card = w) ∧
  (∀ i (D : Finset V), D.card = t → ∃ A ∈ P i, Disjoint D A) ∧
  (∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ B ∈ P j, (A ∩ B).card ≤ 1)

theorem design_blocks_inter_le_one {V : Type*} [DecidableEq V] {k g : ℕ}
    (G : GroupDivisibleDesign V k g) :
    ∀ ⦃A B : Finset V⦄, A ∈ G.blocks → B ∈ G.blocks → A ≠ B → (A ∩ B).card ≤ 1 := by
  intro A B hA hB hne
  by_contra! hcard
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨C, _, hC⟩ := G.cross_group (G.within_group A hA huA hvA huv)
  exact hne ((hC A ⟨hA, huA, hvA⟩).trans (hC B ⟨hB, huB, hvB⟩).symm)

theorem design_block_count {V : Type*} [Fintype V] [DecidableEq V]
    {k g : ℕ} (G : GroupDivisibleDesign V k g) (hk : 2 ≤ k) :
    G.blocks.card = Fintype.card V * (Fintype.card V - g) / (k * (k - 1)) := by
  classical
  let H := packedGraph G.blocks id
  let : DecidableRel H.Adj := Classical.decRel _
  have hdegree (v : V) : H.degree v = Fintype.card V - g := by
    rw [← H.ncard_neighborSet]
    have hneighbors : H.neighborSet v = ({u | G.groups.r v u} : Set V)ᶜ := by
      ext u
      change H.Adj v u ↔ ¬ G.groups.r v u
      rw [packedGraph_adj_iff]
      constructor
      · rintro ⟨B, hB, hv, hu⟩
        obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
        exact G.within_group B hB hv hu hne.symm
      · intro h
        obtain ⟨B, ⟨hB, hv, hu⟩, _⟩ := G.cross_group h
        have hne : u ≠ v := fun he => h (he ▸ G.groups.refl v)
        exact ⟨B, hB, hv, Finset.mem_erase.mpr ⟨hne, hu⟩⟩
    rw [hneighbors, Set.ncard_compl, G.group_card, Nat.card_eq_fintype_card]
  have hsum : (∑ v : V, H.degree v) = Fintype.card V * (Fintype.card V - g) := by
    simp [hdegree]
  have hincidence : (∑ v : V, (G.blocks.filter (fun B => v ∈ B)).card) =
      k * G.blocks.card := by
    simpa only [id_eq] using incidence_sum G.blocks id k G.block_card
  rw [show (∑ v : V, H.degree v) =
      ∑ v : V, (k - 1) * (G.blocks.filter (fun B => v ∈ B)).card by
        exact Finset.sum_congr rfl fun v _ =>
          packedGraph_degree G.blocks id k G.block_card (design_blocks_inter_le_one G) v,
    ← Finset.mul_sum, hincidence] at hsum
  symm
  apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (by omega) (by omega))
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum.symm

private def WSubsets {V : Type*} [DecidableEq V]
    (B : Finset V) (w : ℕ) : Finset (Finset V) :=
  B.powerset.filter (fun A => A.card = w)

private theorem wsubsets_mem_size {V : Type*} [DecidableEq V]
    {B A : Finset V} {w : ℕ} (hA : A ∈ WSubsets B w) : A.card = w := by
  exact (Finset.mem_filter.mp hA).2

private theorem wsubsets_mem_subset {V : Type*} [DecidableEq V]
    {B A : Finset V} {w : ℕ} (hA : A ∈ WSubsets B w) : A ⊆ B := by
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1

private theorem wsubsets_survives_deletion {V : Type*} [DecidableEq V]
    {B : Finset V} {w t : ℕ} (_hB : B.card = w + t)
    (S : Finset V) (_hS : S.card = t) (hwt : w ≤ (B \ S).card) :
    ∃ A ∈ WSubsets B w, Disjoint S A := by
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hwt
  refine ⟨A, ?_, Finset.disjoint_of_subset_right hA ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hA.trans Finset.sdiff_subset), hAcard⟩
  · exact Finset.disjoint_sdiff

private theorem wsubsets_deletion_of_block_size {V : Type*} [DecidableEq V]
    {B : Finset V} {w t : ℕ} (hB : B.card = w + t)
    (S : Finset V) (hS : S.card = t) :
    ∃ A ∈ WSubsets B w, Disjoint S A := by
  apply wsubsets_survives_deletion hB S hS
  rw [Finset.card_sdiff]
  have hinter : (S ∩ B).card ≤ t :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq hS
  omega

private theorem block_support_family
    {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (w t k : ℕ)
    (hblock : ∀ B ∈ blocks, B.card = k)
    (hk : k = w + t)
    (hpairs : ∀ ⦃B B' : Finset V⦄, B ∈ blocks → B' ∈ blocks → B ≠ B' →
      (B ∩ B').card ≤ 1) :
    let I := {B // B ∈ blocks}
    let P : I → Finset (Finset V) := fun B => WSubsets B.1 w
    (∀ i A, A ∈ P i → A.card = w) ∧
    (∀ i S, S.card = t → ∃ A ∈ P i, Disjoint S A) ∧
    (∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ A' ∈ P j,
      (A ∩ A').card ≤ 1) := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro i A hA
    exact wsubsets_mem_size hA
  · intro i S hS
    apply wsubsets_deletion_of_block_size (hblock i.1 i.2 ▸ hk ▸ rfl) S hS
  · intro i j hij A hA A' hA'
    have hblocks : i.1 ≠ j.1 := by
      intro hEq
      exact hij (Subtype.ext hEq)
    have hsub : A ∩ A' ⊆ ((i.val : Finset V) ∩ (j.val : Finset V)) := by
      intro v hv
      have hv' := Finset.mem_inter.mp hv
      exact Finset.mem_inter.mpr
        ⟨wsubsets_mem_subset hA hv'.1, wsubsets_mem_subset hA' hv'.2⟩
    exact (Finset.card_le_card hsub).trans (hpairs i.2 j.2 hblocks)


/-- The leave bound is attained whenever a finite design with the same parameters is supplied. -/
theorem finite_cpecc_support_optimum_of_design
    {V : Type*} [Fintype V] [DecidableEq V]
    (n w t g k : ℕ)
    (hn : Fintype.card V = n) (hkdef : k = w + t) (hkN : k ≤ n)
    (ht : 1 ≤ t) (hw : t + 3 < w) (hg : 1 ≤ g) (hgw : g < w)
    (hRdiv : k - 1 ∣ n - g) (hJdiv : k * (k - 1) ∣ n * (n - g))
    (hthreshold : k * (k + g - 2) ≤ 2 * AppendixA.B w t)
    (G : GroupDivisibleDesign V k g) :
    IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset V), IsSupportFamily P w t}
      (n * (n - g) / (k * (k - 1))) := by
  classical
  let J := n * (n - g) / (k * (k - 1))
  have hcount : G.blocks.card = J := by
    simpa [J, hn] using design_block_count G (by omega)
  let I := {B // B ∈ G.blocks}
  have hI : Fintype.card I = J := (Fintype.card_coe G.blocks).trans hcount
  let e : I ≃ Fin J := Fintype.equivFinOfCardEq hI
  obtain ⟨hsize, hdel, hcross⟩ :=
    block_support_family G.blocks w t k G.block_card hkdef (design_blocks_inter_le_one G)
  refine ⟨⟨fun i => WSubsets (e.symm i).1 w, ?_⟩, ?_⟩
  · refine ⟨fun i => hsize (e.symm i), fun i => hdel (e.symm i), ?_⟩
    intro i j hij
    exact hcross (fun h => hij (e.symm.injective h))
  · rintro m ⟨P, hPsize, hPdel, hPcross⟩
    simpa using finite_cpecc_support_upper_bound P n w t g k
      hn hkdef hkN ht hw hg hgw hRdiv hJdiv hPsize hPdel hPcross hthreshold

private noncomputable def design_of_matching_leave
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (W : I → Finset V) {k : ℕ}
    (hW : ∀ i, (W i).card = k)
    (hdisj : (Set.univ : Set I).Pairwise (fun i j => (W i ∩ W j).card ≤ 1))
    (hmatching : ((packedGraph Finset.univ W)ᶜ.toSubgraph
      (G := (⊤ : SimpleGraph V)) le_top).IsPerfectMatching) :
    GroupDivisibleDesign V k 2 := by
  classical
  let H := packedGraph Finset.univ W
  let L := Hᶜ
  have hunique (u : V) : ∃! v, L.Adj u v :=
    SimpleGraph.Subgraph.isPerfectMatching_iff.mp hmatching u
  have hsame {u a b : V} (ha : L.Adj u a) (hb : L.Adj u b) : a = b := by
    obtain ⟨v, _, hv⟩ := hunique u
    exact (hv a ha).trans (hv b hb).symm
  let groups : Setoid V :=
    { r := fun u v => u = v ∨ L.Adj u v
      iseqv := ⟨fun _ => Or.inl rfl, fun h => h.elim (Or.inl ∘ Eq.symm)
        (Or.inr ∘ SimpleGraph.Adj.symm), fun h₁ h₂ => by
          rcases h₁ with rfl | h₁
          · exact h₂
          rcases h₂ with rfl | h₂
          · exact Or.inr h₁
          exact Or.inl (hsame h₁.symm h₂)⟩ }
  refine
    { groups := groups
      group_card := ?_
      blocks := Finset.univ.image W
      block_card := ?_
      within_group := ?_
      cross_group := ?_ }
  · intro u
    obtain ⟨v, hv, huniq⟩ := hunique u
    have hgroup : {a | groups.r u a} = ({u, v} : Set V) := by
      ext a
      change (u = a ∨ L.Adj u a) ↔ a = u ∨ a = v
      exact ⟨fun h => h.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ fun h => huniq a h),
        fun h => h.elim (Or.inl ∘ Eq.symm) (fun h => Or.inr (h ▸ hv))⟩
    rw [hgroup, Set.ncard_pair hv.ne]
  · intro B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact hW i
  · intro B hB u v hu hv huv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
    have he : H.Adj u v := (packedGraph_adj_iff Finset.univ W u v).mpr
      ⟨i, hi, hu, Finset.mem_erase.mpr ⟨huv.symm, hv⟩⟩
    rintro (h | h)
    · exact huv h
    · exact ((SimpleGraph.compl_adj H u v).mp h).2 he
  · intro u v h
    have huv : u ≠ v := fun he => h (Or.inl he)
    have he : H.Adj u v := by
      by_contra hadj
      exact h (Or.inr ((SimpleGraph.compl_adj H u v).mpr ⟨huv, hadj⟩))
    obtain ⟨i, hi, hui, hvi⟩ := (packedGraph_adj_iff Finset.univ W u v).mp he
    have hvi' := Finset.mem_of_mem_erase hvi
    refine ⟨W i, ⟨Finset.mem_image_of_mem W hi, hui, hvi'⟩, ?_⟩
    intro B ⟨hB, huB, hvB⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    by_contra hne
    have hij : j ≠ i := fun e => hne (congrArg W e)
    have hpair := hdisj (Set.mem_univ j) (Set.mem_univ i) hij
    exact huv (Finset.card_le_one.mp hpair u (Finset.mem_inter.mpr ⟨huB, hui⟩)
      v (Finset.mem_inter.mpr ⟨hvB, hvi'⟩))

private theorem even_strict_edge_threshold {w t : ℕ} (ht : 1 ≤ t)
    (hw : t + 3 < w) (heven : Even t) :
    (w + t) * (w + t) < 2 * AppendixA.B w t := by
  obtain ⟨s, hs⟩ := heven
  let a := w + s - 1
  have ha : w + (t - 1) / 2 = a := by dsimp [a]; omega
  have hb : w + t / 2 = a + 1 := by dsimp [a]; omega
  have hchoose (x : ℕ) : 2 * x.choose 2 = x * (x - 1) := by
    rw [mul_comm, Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self x).two_dvd]
  have hB : 2 * AppendixA.B w t = 2 * a * a := by
    rw [AppendixA.B, ha, hb, Nat.mul_add, hchoose, hchoose]
    have hpred : a = a - 1 + 1 := by dsimp [a]; omega
    rw [Nat.add_sub_cancel]
    nlinarith [congrArg (a * ·) hpred]
  let r := w - (2 * s + 4)
  have hr : w = 2 * s + 4 + r := by dsimp [r]; omega
  have ha' : a = 3 * s + 3 + r := by dsimp [a]; omega
  rw [hB, ha', hr, hs]
  nlinarith

/-- At the even-deletion lengths in the residue-two progression, the stated
upper bound is attained exactly when a design with two-point groups exists. -/
theorem even_residue_optimum_iff_groupDivisibleDesign
    {V : Type*} [Fintype V] [DecidableEq V]
    {n w t : ℕ} (hn : Fintype.card V = n) (hkN : w + t ≤ n)
    (ht : 1 ≤ t) (hw : t + 3 < w) (heven : Even t)
    (hresidue : n % ((w + t) * (w + t - 1)) = 2) :
    let k := w + t
    IsGreatest {m : ℕ | ∃ P : Fin m → Finset (Finset V), IsSupportFamily P w t}
      (n * (n - 2) / (k * (k - 1))) ↔ Nonempty (GroupDivisibleDesign V k 2) := by
  classical
  let k := w + t
  let J := n * (n - 2) / (k * (k - 1))
  change IsGreatest _ J ↔ Nonempty (GroupDivisibleDesign V k 2)
  have hmul : n - 2 = k * (k - 1) * (n / (k * (k - 1))) := by
    have h := Nat.mod_add_div n (k * (k - 1))
    change n % (k * (k - 1)) = 2 at hresidue
    rw [hresidue] at h
    omega
  have hdiv : k * (k - 1) ∣ n - 2 := ⟨_, hmul⟩
  have hRdiv : k - 1 ∣ n - 2 := (Nat.dvd_mul_left (k - 1) k).trans hdiv
  have hJdiv : k * (k - 1) ∣ n * (n - 2) := dvd_mul_of_dvd_right hdiv n
  have hstrict : k * k < 2 * AppendixA.B w t := even_strict_edge_threshold ht hw heven
  constructor
  · rintro ⟨⟨P, hsize, hdel, hcross⟩, _⟩
    obtain ⟨W, hW, hdisj, hmatching⟩ :=
      g2_optimal_support_clique_packing P n w t k hn rfl hkN ht hw hRdiv hJdiv
        hsize hdel hcross hstrict (Fintype.card_fin J)
    exact ⟨design_of_matching_leave W (fun i => (hW i).card_eq) hdisj hmatching⟩
  · rintro ⟨G⟩
    exact finite_cpecc_support_optimum_of_design n w t 2 k hn rfl hkN ht hw
      (by omega) (by omega) hRdiv hJdiv (by simpa using hstrict.le) G

end CPECCBridge
