/- GID: D5/S3/Combinatorics/WeightedBond/PartitionExpansion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WeightedBond/PartitionExpansion
   mirror-E: none(waiver:kernel-checked-source-model)
   anchors: []
   utility: none
   digest: Labeled partition expansion, one-block extensions and coefficient reflection. -/

import D5.S3.Combinatorics.WeightedBond.FiniteOrder
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Polynomial.Reverse

/-! Labeled partition expansion, one-block extensions and coefficient reflection. -/

set_option autoImplicit false

open Finset IncidenceAlgebra

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

abbrev Bonds (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :=
  MultiweightedBond r (SimpleGraph.completeGraph V)

abbrev Weights (r d : ℕ) := ↥(Finset.Nat.antidiagonalTuple r d)

theorem weights_card {r : ℕ} (hr : 0 < r) (d : ℕ) :
    Fintype.card (Weights r d) = (d+r-1).choose (r-1) := by
  let e : Weights r d ≃ Sym (Fin r) d :=
    (Equiv.subtypeEquivRight (fun _ => Finset.Nat.mem_antidiagonalTuple)).trans
      (Sym.equivNatSumOfFintype (Fin r) d).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose, Fintype.card_fin, Nat.add_comm,
    ← Nat.choose_symm (n := d+r-1) (k := d) (by omega)]
  congr 1
  omega

variable (r : ℕ)

abbrev Partitions (V : Type*) [Fintype V] [DecidableEq V] :=
  Finpartition (univ : Finset V)

abbrev Decoration (p : Partitions V) := (B : p.parts) → Weights r (B.val.card - 1)

def decorate (p : Partitions V) (w : Decoration r p) : Bonds V r where
  partition := p
  weight B c := if h : B ∈ p.parts then
    ⟨(w ⟨B, h⟩).val c, by
      have hw := Finset.Nat.mem_antidiagonalTuple.mp (w ⟨B, h⟩).property
      have hc := single_le_sum (f := (w ⟨B,h⟩).val) (fun _ _ => Nat.zero_le _) (mem_univ c)
      change (∑ c, (w ⟨B,h⟩).val c) = B.card - 1 at hw
      have hB := B.card_le_univ
      omega⟩
    else 0
  weight_sum B h := by
    simp only [dite_eq_left h]
    exact Finset.Nat.mem_antidiagonalTuple.mp (w ⟨B, h⟩).property
  weight_off B h c := dite_eq_right h
  connected _ hB := MultiweightedBond.complete_block_connected p hB

def decorationsEquiv : Bonds V r ≃ Σ p : Partitions V, Decoration r p where
  toFun P := ⟨P.partition, fun B => ⟨fun c => P.weight B.val c,
    Finset.Nat.mem_antidiagonalTuple.mpr (P.weight_sum B.val B.property)⟩⟩
  invFun e := decorate r e.1 e.2
  left_inv P := by
    apply MultiweightedBond.ext_weights (P := decorate r P.partition _) (Q := P) rfl
    intro B hB c
    change B ∈ P.partition.parts at hB
    apply Fin.ext
    simp [decorate, hB]
  right_inv e := by
    obtain ⟨p,w⟩ := e
    change Sigma.mk p (fun (B : p.parts) => (⟨fun c => (decorate r p w).weight B.val c, _⟩ : Weights r (B.val.card - 1))) = Sigma.mk p w
    congr 1
    funext B
    apply Subtype.ext
    funext c
    simp [decorate, B.property]

def topPartition (h : 0 < Fintype.card V) : Partitions V :=
  Finpartition.indiscrete (by
    exact Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by simpa using h)))

def topBond (h : 0 < Fintype.card V) (w : Weights r (Fintype.card V - 1)) : Bonds V r where
  partition := topPartition h
  weight B c := if B = univ then
    ⟨w.val c, by
      have hc := single_le_sum (f := w.val) (fun _ _ => Nat.zero_le _) (mem_univ c)
      have hw := Finset.Nat.mem_antidiagonalTuple.mp w.property
      omega⟩
    else 0
  weight_sum B hB := by
    change B ∈ ({univ} : Finset (Finset V)) at hB
    obtain rfl := mem_singleton.mp hB
    simpa using Finset.Nat.mem_antidiagonalTuple.mp w.property
  weight_off B hB c := ite_eq_right (fun he => hB (mem_singleton.mpr he))
  connected _ hB := MultiweightedBond.complete_block_connected _ hB

@[simp] theorem topBond_parts (h : 0 < Fintype.card V)
    (w : Weights r (Fintype.card V - 1)) :
    (topBond r h w).partition.parts = {univ} := rfl

@[simp] theorem topBond_weight (h : 0 < Fintype.card V)
    (w : Weights r (Fintype.card V - 1)) (c : Fin r) :
    ((topBond r h w).weight univ c : ℕ) = w.val c := by
  simp [topBond]

def globalWeight (P : Bonds V r) (c : Fin r) : ℕ :=
  ∑ B ∈ P.partition.parts, (P.weight B c : ℕ)

theorem sum_globalWeight (P : Bonds V r) :
    ∑ c, globalWeight r P c = Fintype.card V - P.partition.parts.card := by
  simp only [globalWeight]
  rw [sum_comm]
  exact P.total_weight_eq_rank

theorem le_topBond_iff (P : Bonds V r) (h : 0 < Fintype.card V)
    (w : Weights r (Fintype.card V - 1)) :
    P ≤ topBond r h w ↔ ∀ c, globalWeight r P c ≤ w.val c := by
  have hs (c : Fin r) :
      P.childSum univ c = globalWeight r P c := by
    simp [MultiweightedBond.childSum, globalWeight,
      D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource.children]
    exact sum_attach _ (fun B : Finset V => (P.weight B c : ℕ))
  have hp : P.partition ≤ (topBond r h w).partition := by
    intro B hB
    exact ⟨univ, by simp, subset_univ B⟩
  constructor
  · intro hle c
    have hh := hle.2 ⟨univ, by simp⟩ c
    simpa [hs] using hh
  · intro hw
    refine ⟨hp, ?_⟩
    intro B c
    have he : B.val = univ := by simpa using B.property
    simpa only [he, hs, topBond_weight] using hw c

theorem parts_pos (P : Bonds V r) (h : 0 < Fintype.card V) :
    0 < P.partition.parts.card := by
  by_contra! hn
  have hh := P.partition.sum_card_parts
  rw [card_eq_zero.mp (Nat.eq_zero_of_le_zero hn), sum_empty, card_univ] at hh
  omega

/-- The increments in a one-block extension are freely chosen. -/
def topExtensions (P : Bonds V r) (h : 0 < Fintype.card V) :
    {w : Weights r (Fintype.card V - 1) // P ≤ topBond r h w} ≃
      Weights r (P.partition.parts.card - 1) where
  toFun w := by
    have hw := (le_topBond_iff r P h w.val).mp w.property
    refine ⟨fun c => w.val.val c - globalWeight r P c, ?_⟩
    rw [Finset.Nat.mem_antidiagonalTuple, sum_tsub_distrib _ (fun c _ => hw c), sum_globalWeight]
    have hh := Finset.Nat.mem_antidiagonalTuple.mp w.val.property
    have hk := P.partition.card_parts_le_card
    have hp := parts_pos r P h
    rw [card_univ] at hk
    omega
  invFun d := by
    let w : Weights r (Fintype.card V - 1) := ⟨fun c => globalWeight r P c + d.val c, by
      rw [Finset.Nat.mem_antidiagonalTuple, sum_add_distrib, sum_globalWeight]
      have hd := Finset.Nat.mem_antidiagonalTuple.mp d.property
      have hk := P.partition.card_parts_le_card
      have hp := parts_pos r P h
      rw [card_univ] at hk
      omega⟩
    exact ⟨w, (le_topBond_iff r P h w).mpr fun c => Nat.le_add_right _ _⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext c
    exact Nat.add_sub_of_le ((le_topBond_iff r P h w.val).mp w.property c)
  right_inv d := by
    apply Subtype.ext
    funext c
    exact Nat.add_sub_cancel_left _ _

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false

open Finset IncidenceAlgebra
open D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource (children)

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private def blockMap (e : V ≃ W) : Finset V ≃o Finset W :=
  { e.finsetCongr with map_rel_iff' := map_subset_map }

def relabelPartition (e : V ≃ W) (p : Partitions V) : Partitions W :=
  (p.map (blockMap e)).copy (by
    change univ.map e.toEmbedding = univ
    ext b
    simp)

@[simp] theorem relabel_parts (e : V ≃ W) (p : Partitions V) :
    (relabelPartition e p).parts = p.parts.map e.finsetCongr.toEmbedding := rfl

@[simp] private theorem blockMap_mem (e : V ≃ W) (p : Partitions V) (B : Finset V) :
    e.finsetCongr B ∈ (relabelPartition e p).parts ↔ B ∈ p.parts := by
  rw [relabel_parts]
  exact Finset.mem_map' (f := e.finsetCongr.toEmbedding)

@[simp] theorem relabelPartition_symm (e : V ≃ W) (p : Partitions V) :
    relabelPartition e.symm (relabelPartition e p) = p := by
  ext B
  conv_lhs => rw [show B = e.symm.finsetCongr (e.finsetCongr B) from (e.finsetCongr.symm_apply_apply B).symm]
  rw [blockMap_mem, blockMap_mem]

def relabel (e : V ≃ W) {r : ℕ} (P : Bonds V r) : Bonds W r where
  partition := relabelPartition e P.partition
  weight B c := finCongr (congrArg (· + 1) (Fintype.card_congr e))
    (P.weight (e.symm.finsetCongr B) c)
  weight_sum B hB := by
    obtain ⟨A, rfl⟩ := e.finsetCongr.surjective B
    rw [blockMap_mem] at hB
    change (∑ c, (P.weight (e.symm.finsetCongr (e.finsetCongr A)) c : ℕ)) = _
    rw [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply]
    simpa only [Equiv.finsetCongr_apply, card_map] using P.weight_sum A hB
  weight_off B hB c := by
    obtain ⟨A, rfl⟩ := e.finsetCongr.surjective B
    rw [blockMap_mem] at hB
    apply Fin.ext
    change (P.weight (e.symm.finsetCongr (e.finsetCongr A)) c : ℕ) = 0
    rw [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply, P.weight_off A hB c]
    rfl
  connected _ h := MultiweightedBond.complete_block_connected _ h

@[simp] theorem relabel_weight {r : ℕ} (e : V ≃ W) (P : Bonds V r)
    (B : Finset V) (c : Fin r) :
    ((relabel e P).weight (e.finsetCongr B) c : ℕ) = P.weight B c := by
  change (P.weight (e.symm.finsetCongr (e.finsetCongr B)) c : ℕ) = _
  rw [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply]

private theorem relabel_symm {r : ℕ} (e : V ≃ W) (P : Bonds V r) :
    relabel e.symm (relabel e P) = P := by
  apply MultiweightedBond.ext_weights (relabelPartition_symm e P.partition)
  intro B _ c
  apply Fin.ext
  calc
    _ = ((relabel e.symm (relabel e P)).weight (e.symm.finsetCongr (e.finsetCongr B)) c : ℕ) := by
      rw [← Equiv.finsetCongr_symm, Equiv.symm_apply_apply]
    _ = _ := by rw [relabel_weight, relabel_weight]

private theorem childSum_relabel {r : ℕ} (e : V ≃ W) (P : Bonds V r)
    (B : Finset V) (c : Fin r) :
    (relabel e P).childSum (e.finsetCongr B) c = P.childSum B c := by
  have h (A : Finset V) : e.finsetCongr A ⊆ e.finsetCongr B ↔ A ⊆ B := map_subset_map
  simp only [MultiweightedBond.childSum, children]
  rw [sum_filter, sum_filter, sum_attach _ (fun D => if D ⊆ e.finsetCongr B then
    ((relabel e P).weight D c : ℕ) else 0), sum_attach _ (fun D => if D ⊆ B then
    (P.weight D c : ℕ) else 0)]
  change (∑ D ∈ (relabelPartition e P.partition).parts, _) = _
  rw [relabel_parts, sum_map]
  simp only [Equiv.toEmbedding_apply, h, relabel_weight]

private theorem relabel_monotone {r : ℕ} (e : V ≃ W) :
    Monotone (relabel (r := r) e) := by
  intro P Q h
  refine ⟨?_, ?_⟩
  · intro B hB
    obtain ⟨A, rfl⟩ := e.finsetCongr.surjective B
    obtain ⟨D, hD, hAD⟩ := h.1 ((blockMap_mem e P.partition A).mp hB)
    exact ⟨e.finsetCongr D, (blockMap_mem e Q.partition D).mpr hD,
      map_subset_map.mpr hAD⟩
  · intro B c
    obtain ⟨A, he⟩ := e.finsetCongr.surjective B.val
    have hA : A ∈ Q.partition.parts :=
      (blockMap_mem e Q.partition A).mp (he ▸ B.property)
    change (relabel e P).childSum B.val c ≤ ((relabel e Q).weight B.val c : ℕ)
    rw [← he, childSum_relabel, relabel_weight]
    exact h.2 ⟨A, hA⟩ c

def relabelOrderIso {r : ℕ} (e : V ≃ W) : Bonds V r ≃o Bonds W r where
  toFun := relabel e
  invFun := relabel e.symm
  left_inv := relabel_symm e
  right_inv := relabel_symm e.symm
  map_rel_iff' := by
    intro P Q
    change relabel e P ≤ relabel e Q ↔ P ≤ Q
    refine ⟨fun h => ?_, fun h => relabel_monotone e h⟩
    simpa only [relabel_symm] using relabel_monotone e.symm h

private theorem mu_bot_relabel {r : ℕ} (e : V ≃ W) (P : Bonds V r) :
    mu ℤ ⊥ (relabel e P) = mu ℤ ⊥ P :=
  (MultiweightedBond.mu_bot_orderIso (relabelOrderIso e) P).symm

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 500

open Finset IncidenceAlgebra

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private def finTop (r n : ℕ) (h : 0 < n) (w : Weights r (n-1)) : Bonds (Fin n) r :=
  topBond r (by simpa using h)
    ⟨w.val, by simpa only [Fintype.card_fin] using w.property⟩

def muComplete (r n : ℕ) : ℤ :=
  if h : 0 < n then
    ∑ w : Weights r (n - 1), mu ℤ ⊥ (finTop r n h w)
  else 0

private theorem muComplete_pos (r n : ℕ) (h : 0 < n) :
    muComplete r n =
      ∑ w : Weights r (n - 1), mu ℤ ⊥ (finTop r n h w) := by
  simp only [muComplete, dite_eq_left h]

private def regraph {r : ℕ} {G H : SimpleGraph V} (h : G = H)
    (P : MultiweightedBond r G) : MultiweightedBond r H := h ▸ P

private theorem regraph_partition {r : ℕ} {G H : SimpleGraph V} (h : G = H)
    (P : MultiweightedBond r G) : (regraph h P).partition = P.partition := by
  cases h
  rfl

private theorem regraph_weight {r : ℕ} {G H : SimpleGraph V} (h : G = H)
    (P : MultiweightedBond r G) (B : Finset V) (c : Fin r) :
    (regraph h P).weight B c = P.weight B c := by
  cases h
  rfl

private theorem mu_regraph {r : ℕ} {G H : SimpleGraph V} (h : G = H)
    (P : MultiweightedBond r G) : mu ℤ ⊥ (regraph h P) = mu ℤ ⊥ P := by
  cases h
  rfl

omit [DecidableEq V] in
private theorem relabel_univ {W : Type*} [Fintype W] (e : V ≃ W) :
    e.finsetCongr univ = univ := by
  ext b
  simp

private theorem block_mu (r : ℕ) (p : Partitions V) (w : Decoration r p) (B : p.parts) :
    mu ℤ ⊥ (MultiweightedBond.oneBlock (decorate r p w) B) =
      mu ℤ ⊥ (finTop r B.val.card (p.nonempty_of_mem_parts B.property).card_pos (w B)) := by
  let Q := MultiweightedBond.oneBlock (decorate r p w) B
  let R := regraph (SimpleGraph.induce_top (B.val : Set V)) Q
  let e : (B.val : Set V) ≃ Fin B.val.card := B.val.equivFin
  rw [← mu_regraph (SimpleGraph.induce_top (B.val : Set V)) Q, ← mu_bot_relabel e R]
  apply congrArg (mu ℤ ⊥)
  have hp : (relabel e R).partition.parts = {univ} := by
    change (relabelPartition e R.partition).parts = _
    have hQ : Q.partition.parts = {univ} := MultiweightedBond.oneBlock_parts (decorate r p w) B
    rw [relabel_parts, show R.partition = Q.partition from regraph_partition _ _, hQ, map_singleton]
    exact congrArg singleton (relabel_univ e)
  have ht : (finTop r B.val.card (p.nonempty_of_mem_parts B.property).card_pos (w B)).partition.parts =
      {univ} := rfl
  apply MultiweightedBond.ext_weights (Finpartition.ext (hp.trans ht.symm))
  intro A hA c
  rw [hp] at hA
  obtain rfl := mem_singleton.mp hA
  apply Fin.ext
  have hR : (R.weight univ c : ℕ) = (w B).val c := by
    dsimp only [R]
    rw [regraph_weight]
    have hQ : (Q.weight univ c : ℕ) = (decorate r p w).weight B.val c :=
      MultiweightedBond.oneBlock_weight (decorate r p w) B c
    rw [hQ]
    simp [decorate, B.property]
  calc
    _ = ((relabel e R).weight (e.finsetCongr univ) c : ℕ) := by rw [relabel_univ]
    _ = _ := by rw [relabel_weight, hR, finTop, topBond_weight]

def partitionProduct (r : ℕ) (p : Partitions V) : ℤ :=
  ∏ B ∈ p.parts, muComplete r B.card

/-- Grouping the actual carrier by the labeled partition gives independent block sums. -/
theorem sum_mu_grouped (r : ℕ) {R : Type*} [CommRing R] (a : Partitions V → R) :
    (∑ P : Bonds V r, (mu ℤ ⊥ P : R) * a P.partition) =
      ∑ p : Partitions V, (partitionProduct r p : R) * a p := by
  calc
    _ = ∑ d : (Σ p : Partitions V, Decoration r p),
        (mu ℤ ⊥ (decorate r d.1 d.2) : R) * a d.1 := by
      apply Fintype.sum_equiv (decorationsEquiv r)
      intro P
      change _ = (mu ℤ ⊥ ((decorationsEquiv r).symm ((decorationsEquiv r) P)) : R) * _
      rw [Equiv.symm_apply_apply]
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro p _
      change (∑ w : Decoration r p, (mu ℤ ⊥ (decorate r p w) : R) * a p) = _
      rw [← sum_mul, ← Int.cast_sum]
      congr 2
      have hproduct : (∑ w : Decoration r p, mu ℤ ⊥ (decorate r p w)) =
          ∑ w : Decoration r p, ∏ B : p.parts,
            mu ℤ ⊥ (MultiweightedBond.oneBlock (decorate r p w) B) :=
        sum_congr rfl fun w _ => MultiweightedBond.mu_bot_eq_prod_blocks (decorate r p w)
      rw [hproduct]
      simp_rw [block_mu]
      let f (B : p.parts) (x : Weights r (B.val.card - 1)) :=
        mu ℤ ⊥ (finTop r B.val.card (p.nonempty_of_mem_parts B.property).card_pos x)
      change (∑ w : Decoration r p, ∏ B : p.parts, f B (w B)) = _
      rw [← Fintype.prod_sum f]
      unfold partitionProduct
      rw [← prod_coe_sort p.parts (fun B : Finset V => muComplete r B.card)]
      apply prod_congr rfl
      intro B _
      rw [muComplete_pos _ _ (p.nonempty_of_mem_parts B.property).card_pos]

theorem psiComplete_partition (n r : ℕ) :
    psiComplete n r = ∑ p : Partitions (Fin n),
      Polynomial.C (partitionProduct r p : ℚ) * Polynomial.X ^ (n - p.parts.card) := by
  have h := sum_mu_grouped (V := Fin n) r (R := Polynomial ℚ)
    (fun p => Polynomial.X ^ (n - p.parts.card))
  simpa only [psiComplete, map_intCast] using h

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 500

open Finset IncidenceAlgebra

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem topBond_eq_bot_iff (r : ℕ) (h : 0 < Fintype.card V)
    (w : Weights r (Fintype.card V - 1)) :
    (⊥ : Bonds V r) = topBond r h w ↔ Fintype.card V = 1 := by
  constructor
  · intro he
    have hc := congrArg (fun P : Bonds V r => P.partition.parts.card) he
    change (⊥ : Partitions V).parts.card = (topBond r h w).partition.parts.card at hc
    simpa [Finpartition.card_bot] using hc
  · intro hn
    have hU : (univ : Finset V).card = 1 := by simpa using hn
    obtain ⟨v, hv⟩ := card_eq_one.mp hU
    have hp : (⊥ : Bonds V r).partition = (topBond r h w).partition := by
      apply Finpartition.ext
      rw [topBond_parts]
      change (⊥ : Partitions V).parts = _
      simp [Finpartition.parts_bot, hv]
    apply MultiweightedBond.ext_weights hp
    intro B hB c
    have he : B = univ := by simpa [hp] using hB
    rw [he]
    exact ((topBond r h w).weight_eq_zero_of_card_one (by simp) hU c).symm

private def intervalPairs (r : ℕ) (h : 0 < Fintype.card V) :
    (Σ w : Weights r (Fintype.card V - 1), Set.Iic (topBond r h w)) ≃
      Σ P : Bonds V r, {w : Weights r (Fintype.card V - 1) // P ≤ topBond r h w} where
  toFun x := ⟨x.2.val, x.1, x.2.property⟩
  invFun x := ⟨x.2.val, x.1, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete-graph inverse relation before applying the exponential formula. -/
theorem partition_inverse_recurrence (r : ℕ) (hr : 0 < r) (n : ℕ) (hn : 0 < n) :
    (∑ p : Partitions (Fin n), partitionProduct r p *
      (((p.parts.card - 1 + r - 1).choose (r - 1) : ℕ) : ℤ)) =
      if n = 1 then 1 else 0 := by
  let V := Fin n
  have h : 0 < Fintype.card V := by simpa [V] using hn
  have hm (w : Weights r (Fintype.card V - 1)) :
      (∑ P : Set.Iic (topBond r h w), mu ℤ ⊥ P.val) = if n = 1 then 1 else 0 := by
    calc
      _ = ∑ P : ↥(Icc (⊥ : Bonds V r) (topBond r h w)), mu ℤ ⊥ P.val :=
        Fintype.sum_equiv (Equiv.subtypeEquivRight (fun P => by
          change P ≤ topBond r h w ↔ P ∈ Icc ⊥ (topBond r h w)
          simp)) _ _ (fun _ => rfl)
      _ = _ := by
        rw [sum_coe_sort, sum_Icc_mu_right]
        exact if_congr (show (⊥ : Bonds V r) = topBond r h w ↔ n = 1 by
          simpa [V] using topBond_eq_bot_iff r h w) rfl rfl
  have hs : (∑ w : Weights r (Fintype.card V - 1),
        ∑ P : Set.Iic (topBond r h w), mu ℤ ⊥ P.val) =
      ∑ P : Bonds V r, mu ℤ ⊥ P *
        (((P.partition.parts.card - 1 + r - 1).choose (r - 1) : ℕ) : ℤ) := by
    calc
      _ = ∑ q : (Σ P : Bonds V r, {w : Weights r (Fintype.card V - 1) // P ≤ topBond r h w}),
          mu ℤ ⊥ q.1 := by
        let f : (Σ w : Weights r (Fintype.card V - 1), Set.Iic (topBond r h w)) → ℤ :=
          fun x => mu ℤ ⊥ x.2.val
        change (∑ w, ∑ P, f ⟨w, P⟩) = _
        rw [← Fintype.sum_sigma]
        exact Fintype.sum_equiv (intervalPairs r h) _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply sum_congr rfl
        intro P _
        change (∑ _ : {w : Weights r (Fintype.card V - 1) // P ≤ topBond r h w},
          mu ℤ ⊥ P) = _
        rw [sum_const, card_univ, Fintype.card_congr (topExtensions r P h), weights_card hr,
          nsmul_eq_mul, mul_comm]
  have ht := sum_mu_grouped (V := V) r (R := ℤ)
    (fun p => (((p.parts.card - 1 + r - 1).choose (r - 1) : ℕ) : ℤ))
  simp only [Int.cast_id] at ht
  rw [← ht, ← hs]
  simp_rw [hm]
  split_ifs with he
  · rw [sum_const, card_univ, weights_card hr]
    simp [V, he]
  · simp

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false
open Finset IncidenceAlgebra

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

def reversePsi (n r : ℕ) : Polynomial ℚ :=
  ∑ P : CompleteBond n r,
    Polynomial.C (mu ℤ ⊥ P : ℚ) * Polynomial.X ^ (P.partition.parts.card - 1)

theorem reversePsi_eq_reflect {n : ℕ} (hn : 0 < n) (r : ℕ) :
    reversePsi n r = Polynomial.reflect (n - 1) (psiComplete n r) := by
  classical
  unfold reversePsi psiComplete
  let reflect : Polynomial ℚ →+ Polynomial ℚ :=
    { toFun := Polynomial.reflect (n - 1)
      map_zero' := Polynomial.reflect_zero
      map_add' := fun a b => Polynomial.reflect_add a b (n - 1) }
  change _ = reflect (∑ P : CompleteBond n r,
    Polynomial.C (mu ℤ ⊥ P : ℚ) * Polynomial.X ^ (n - P.partition.parts.card))
  rw [map_sum]
  apply sum_congr rfl
  intro P _
  change _ = Polynomial.reflect (n - 1) (Polynomial.C (mu ℤ ⊥ P : ℚ) * Polynomial.X ^ (n - P.partition.parts.card))
  rw [Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le]
  · have hk : P.partition.parts.card ≤ n := by simpa using P.partition.card_parts_le_card
    have hp := parts_pos r P (by simpa using hn)
    congr 2
    omega
  · have hp := parts_pos r P (by simpa using hn)
    omega

end
end D5.S3.Combinatorics.WeightedBond
