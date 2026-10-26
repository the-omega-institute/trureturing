/- GID: D5/S3/Combinatorics/Sequenceability/PositiveChargeGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PositiveChargeGeometry
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original integer incidence and positive component charge yield coefficient-one primitive ledgers or an all-coordinate avoiding permutation. -/

import D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
import D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
import D5.S3.Combinatorics.Graph.EdgeColouring.TwoColours
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

/-! Original Boolean incidence determines positive-charge geometry.

The signed ordinary-component gcd equal to the terminal count forces a
component containing all terminals on one side. The original q equation
makes its potential injective. Disjoint minimal Boolean decomposition
excludes negative selected potentials; two integer potentials identify the
terminal side and force common-neighbour coverage. The original-coordinate
colouring and universal/nonuniversal word constructions retain every ID.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
namespace PositiveChargeGeometry
open scoped BigOperators Classical
open Finset
open D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
open DisjointMinimalZeroOrdering (MinimalZeroSupport zero_decomposition_pairwise_disjoint)
universe u
variable {X : Type u} [DecidableEq X]
variable {M : Submodule ℤ (X → ℤ)} {Ω : Finset X} {q : X}

/- The quotient adapter consumes the NEW disjoint supplier. In particular,
   it never recursively rebuilds a competing decomposition proof. -/

private theorem row_eq_sum_single (S : Finset X) :
    row S = ∑ x ∈ S, Pi.single x (1 : ℤ) := by
  ext x
  simp [row, Pi.single_apply]

def quotientLabel (M : Submodule ℤ (X → ℤ)) (x : X) : (X → ℤ) ⧸ M :=
  M.mkQ (Pi.single x 1)

theorem quotient_zero_iff (S : Finset X) :
    (∑ x ∈ S, quotientLabel M x) = 0 ↔ row S ∈ M := by
  rw [row_eq_sum_single]
  simpa only [quotientLabel, ← map_sum, Submodule.mkQ_apply] using
    (Submodule.Quotient.mk_eq_zero (p := M)
      (x := ∑ x ∈ S, Pi.single x (1 : ℤ)))

private theorem quotient_minimal_iff {S : Finset X}
    (hSΩ : S ⊆ Ω) (hproper : S ≠ Ω) :
    MinimalZeroSupport (quotientLabel M) S ↔ Minimal M Ω S := by
  constructor
  · rintro ⟨hne, hz, hmin⟩
    refine ⟨⟨hSΩ, hne, hproper, (quotient_zero_iff S).mp hz⟩, ?_⟩
    intro B hB hBS
    exact hmin B hBS hB.2.1 ((quotient_zero_iff B).mpr hB.2.2.2)
  · rintro ⟨hC, hmin⟩
    refine ⟨hC.2.1, (quotient_zero_iff S).mpr hC.2.2.2, ?_⟩
    intro B hBS hne hz
    apply hmin B _ hBS
    refine ⟨hBS.trans hSΩ, hne, ?_, (quotient_zero_iff B).mp hz⟩
    intro he
    exact hproper (hSΩ.antisymm (he ▸ hBS))

/-- For EVERY actual Complete row, the original coefficient-one indicator is
a sum of pairwise disjoint ORIGINAL minimal indicators. This is the adapter
consumed by the negative-selector inference and the existing native endpoint. -/
theorem complete_disjoint_decomposition {A : Finset X} (hA : Complete M Ω A) :
    ∃ Q : Finset (Finset X), Q ⊆ minimalFamily M Ω ∧ Independent Q ∧
      A = Q.biUnion id ∧ row A = ∑ S ∈ Q, row S := by
  obtain ⟨Q, hQ, hdis, hcover⟩ := zero_decomposition_pairwise_disjoint
    (quotientLabel M) Ω A hA.1 ((quotient_zero_iff A).mpr hA.2.2.2)
  have hQA {S : Finset X} (hS : S ∈ Q) : S ⊆ A := by
    intro x hx
    rw [hcover]
    exact mem_biUnion.mpr ⟨S, hS, hx⟩
  refine ⟨Q, ?_, ?_, hcover, ?_⟩
  · intro S hS
    apply mem_minimalFamily.mpr
    refine ⟨(hQ S hS).1, (quotient_minimal_iff (hQ S hS).1 ?_).mp (hQ S hS).2⟩
    intro he
    exact hA.2.2.1 (hA.1.antisymm (he ▸ hQA hS))
  · intro S hS D hD hSD
    exact hdis hS hD hSD
  · simp_rw [row_eq_sum_single]
    rw [hcover]
    exact Finset.sum_biUnion hdis

/-- Actual integer potential, not a projected ordinary-edge map. -/
def potential (M : Submodule ℤ (X → ℤ)) (Ω : Finset X)
    (a : Finset X → ℤ) : X → ℤ :=
  ∑ S ∈ minimalFamily M Ω, a S • row S

theorem potential_apply (a : Finset X → ℤ) (x : X) :
    potential M Ω a x = ∑ S ∈ neighborhood M Ω x, a S := by
  simp [potential, neighborhood, row, Finset.sum_apply, Finset.sum_filter,
    smul_eq_mul, mul_ite]

theorem potential_mem (a : Finset X → ℤ) : potential M Ω a ∈ M := by
  apply M.sum_mem
  intro S hS
  exact M.smul_mem _ (mem_minimalFamily.mp hS).2.1.2.2.2

theorem potential_outside (a : Finset X → ℤ) {x : X} (hx : x ∉ Ω) :
    potential M Ω a x = 0 := by
  rw [potential_apply]
  apply sum_eq_zero
  intro S hS
  exact (hx ((mem_minimalFamily.mp (mem_neighborhood.mp hS).1).1
    (mem_neighborhood.mp hS).2)).elim

theorem potential_pair (a : Finset X → ℤ) {x : X} {s t : Finset X}
    (hst : s ≠ t) (hx : neighborhood M Ω x = {s,t}) :
    potential M Ω a x = a s + a t := by
  rw [potential_apply, hx]
  simp [hst]

private theorem potential_selector {Q : Finset (Finset X)}
    (hQ : Q ⊆ minimalFamily M Ω) :
    potential M Ω (fun S => if S ∈ Q then 1 else 0) = ∑ S ∈ Q, row S := by
  simp only [potential, ite_smul, one_smul, zero_smul]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp only [mem_filter]
  exact ⟨And.right, fun h => ⟨hQ h, h⟩⟩

/- Finite H ledgers are obtained from span membership itself. There is no
   input ledger and no division of a scaled certificate. -/
theorem original_ledger {H : Finset (Finset X)} {z : X → ℤ}
    (hz : z ∈ originalSpan H) :
    ∃ c : Finset X → ℤ, z = ∑ h ∈ H, c h • row h := by
  apply Submodule.span_induction (p := fun z _ =>
    ∃ c : Finset X → ℤ, z = ∑ h ∈ H, c h • row h) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨fun k => if k = h then 1 else 0, ?_⟩
    simp [hh]
  · exact ⟨fun _ => 0, by simp⟩
  · intro x y hx hy cx cy
    obtain ⟨a, rfl⟩ := cx
    obtain ⟨b, rfl⟩ := cy
    refine ⟨fun h => a h + b h, ?_⟩
    simp [add_smul, sum_add_distrib]
  · intro n x hx cx
    obtain ⟨a, rfl⟩ := cx
    exact ⟨fun h => n * a h, by simp [mul_smul, Finset.smul_sum]⟩

/- Raw, original-coordinate component inventory. -/

def OrdinaryAdj (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (s t : Finset X) : Prop :=
  s ∈ minimalFamily M Ω ∧ t ∈ minimalFamily M Ω ∧ s ≠ t ∧
    ∃ x, x ≠ q ∧ x ∈ s ∧ x ∈ t

/-- A connected ungrounded bipartite ordinary component, in either orientation.
`port` retains the exact original twice-occurring ID and all its incidences.
It is the incidence formulation of ungroundedness, component closure and
bipartiteness, rather than any of the desired positive geometry conclusions. -/
structure RawBlock (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (A B : Finset (Finset X)) : Prop where
  left_minimal : A ⊆ minimalFamily M Ω
  right_minimal : B ⊆ minimalFamily M Ω
  disjoint : Disjoint A B
  nonempty : (A ∪ B).Nonempty
  connected : ∀ s ∈ A ∪ B, ∀ t ∈ A ∪ B,
    Relation.ReflTransGen (OrdinaryAdj M Ω q) s t
  port : ∀ v ∈ A ∪ B, ∀ x ∈ v, x ≠ q →
    ∃ a ∈ A, ∃ b ∈ B, neighborhood M Ω x = {a,b}

def signedCharge (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (A B : Finset (Finset X)) : ℤ :=
  ((neighborhood M Ω q ∩ A).card : ℤ) - (neighborhood M Ω q ∩ B).card

def blockInventory (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X) :
    Finset (Finset (Finset X) × Finset (Finset X)) :=
  ((minimalFamily M Ω).powerset ×ˢ (minimalFamily M Ω).powerset).filter
    (fun p => RawBlock M Ω q p.1 p.2)

/-- The ordinary-component charge gcd. Both orientations are enumerated;
their duplicated absolute charges have the same gcd. All vertices in this
finite inventory are literal original minimal supports. -/
def chargeGCD (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X) : ℕ :=
  (blockInventory M Ω q).gcd (fun p => (signedCharge M Ω q p.1 p.2).natAbs)

private theorem mem_inventory {A B : Finset (Finset X)} :
    (A,B) ∈ blockInventory M Ω q ↔ RawBlock M Ω q A B := by
  simp only [blockInventory, mem_filter, mem_product, mem_powerset]
  exact ⟨And.right, fun h => ⟨⟨h.left_minimal,h.right_minimal⟩,h⟩⟩

theorem RawBlock.swap {A B : Finset (Finset X)} (h : RawBlock M Ω q A B) :
    RawBlock M Ω q B A := by
  refine ⟨h.right_minimal,h.left_minimal,h.disjoint.symm,?_,?_,?_⟩
  · simpa [union_comm] using h.nonempty
  · simpa [union_comm] using h.connected
  · intro v hv x hx hxq
    obtain ⟨a,ha,b,hb,he⟩ := h.port v (by simpa [union_comm] using hv) x hx hxq
    exact ⟨b,hb,a,ha,by simpa [Finset.pair_comm] using he⟩

private theorem charge_bound {A B : Finset (Finset X)} (h : RawBlock M Ω q A B) :
    (signedCharge M Ω q A B).natAbs ≤ (neighborhood M Ω q).card := by
  have ha := card_le_card (inter_subset_left : neighborhood M Ω q ∩ A ⊆ _)
  have hb := card_le_card (inter_subset_left : neighborhood M Ω q ∩ B ⊆ _)
  have hc : |signedCharge M Ω q A B| ≤ ((neighborhood M Ω q).card : ℤ) := by
    apply abs_le.mpr
    dsimp [signedCharge]
    have ha' : ((neighborhood M Ω q ∩ A).card : ℤ) ≤
        (neighborhood M Ω q).card := by exact_mod_cast ha
    have hb' : ((neighborhood M Ω q ∩ B).card : ℤ) ≤
        (neighborhood M Ω q).card := by exact_mod_cast hb
    constructor <;> omega
  have hc' : ((signedCharge M Ω q A B).natAbs : ℤ) ≤
      (neighborhood M Ω q).card := by simpa only [Int.natCast_natAbs] using hc
  exact_mod_cast hc'

/-- Actual positive charge selects a genuine original raw component; no block
or terminal localization is an extra theorem premise. -/
theorem positive_charge_block
    (hr : 0 < (neighborhood M Ω q).card)
    (hd : chargeGCD M Ω q = (neighborhood M Ω q).card) :
    ∃ A B, RawBlock M Ω q A B ∧
      signedCharge M Ω q A B = ((neighborhood M Ω q).card : ℤ) := by
  have hnz : chargeGCD M Ω q ≠ 0 := by omega
  obtain ⟨p,hp,hpc⟩ : ∃ p ∈ blockInventory M Ω q,
      (signedCharge M Ω q p.1 p.2).natAbs ≠ 0 := by
    by_contra h
    apply hnz
    apply Finset.gcd_eq_zero_iff.mpr
    intro p hp
    by_contra hc
    exact h ⟨p,hp,hc⟩
  have hraw := mem_inventory.mp hp
  have hdiv : (neighborhood M Ω q).card ∣
      (signedCharge M Ω q p.1 p.2).natAbs := by
    rw [← hd]
    exact Finset.gcd_dvd hp
  have hle := charge_bound hraw
  have hge := Nat.le_of_dvd (Nat.pos_of_ne_zero hpc) hdiv
  have he : (signedCharge M Ω q p.1 p.2).natAbs =
      (neighborhood M Ω q).card := by omega
  have heabs : |signedCharge M Ω q p.1 p.2| =
      ((neighborhood M Ω q).card : ℤ) := by
    simpa only [Int.natCast_natAbs] using congrArg (fun n : ℕ => (n : ℤ)) he
  by_cases hc : 0 ≤ signedCharge M Ω q p.1 p.2
  · rw [abs_of_nonneg hc] at heabs
    exact ⟨p.1,p.2,hraw,heabs⟩
  · rw [abs_of_neg (by omega)] at heabs
    refine ⟨p.2,p.1,hraw.swap,?_⟩
    dsimp [signedCharge] at *
    omega

theorem RawBlock.terminals_left {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B)
    (hc : signedCharge M Ω q A B = ((neighborhood M Ω q).card : ℤ)) :
    neighborhood M Ω q ⊆ A := by
  have hle := card_le_card
    (inter_subset_left : neighborhood M Ω q ∩ A ⊆ neighborhood M Ω q)
  have hcard : (neighborhood M Ω q ∩ A).card = (neighborhood M Ω q).card := by
    dsimp [signedCharge] at hc
    omega
  have he : neighborhood M Ω q ∩ A = neighborhood M Ω q :=
    eq_of_subset_of_card_le inter_subset_left (by omega)
  intro t ht
  exact (mem_inter.mp (he.symm ▸ ht)).2

private theorem RawBlock.left_ne_right {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) {a b : Finset X} (ha : a ∈ A) (hb : b ∈ B) : a ≠ b := by
  rintro rfl
  exact Finset.disjoint_left.mp h.disjoint ha hb

private theorem RawBlock.step {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) {s t : Finset X}
    (hs : s ∈ A ∪ B) (hst : OrdinaryAdj M Ω q s t) :
    t ∈ A ∪ B ∧ ((s ∈ A ∧ t ∈ B) ∨ (s ∈ B ∧ t ∈ A)) ∧
      ∃ x, neighborhood M Ω x = {s,t} := by
  obtain ⟨hsV,htV,hne,x,hxq,hxs,hxt⟩ := hst
  obtain ⟨a,ha,b,hb,hN⟩ := h.port s hs x hxs hxq
  have hsN : s ∈ ({a,b} : Finset (Finset X)) := by
    rw [← hN]; exact mem_neighborhood.mpr ⟨hsV,hxs⟩
  have htN : t ∈ ({a,b} : Finset (Finset X)) := by
    rw [← hN]; exact mem_neighborhood.mpr ⟨htV,hxt⟩
  simp only [mem_insert, mem_singleton] at hsN htN
  rcases hsN with rfl | rfl <;> rcases htN with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨mem_union_right _ hb,Or.inl ⟨ha,hb⟩,x,hN⟩
  · exact ⟨mem_union_left _ ha,Or.inr ⟨hb,ha⟩,x,
      by simpa [Finset.pair_comm] using hN⟩
  · exact (hne rfl).elim

private theorem RawBlock.no_same_left {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) {s t : Finset X} (hs : s ∈ A) (ht : t ∈ A) :
    ¬ OrdinaryAdj M Ω q s t := by
  intro hadj
  rcases (h.step (mem_union_left _ hs) hadj).2.1 with hab | hba
  · exact Finset.disjoint_left.mp h.disjoint ht hab.2
  · exact Finset.disjoint_left.mp h.disjoint hs hba.1

private theorem RawBlock.no_q_right {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hT : neighborhood M Ω q ⊆ A)
    {b : Finset X} (hb : b ∈ B) : q ∉ b := by
  intro hqb
  exact Finset.disjoint_left.mp h.disjoint
    (hT (mem_neighborhood.mpr ⟨h.right_minimal hb,hqb⟩)) hb

/- Integer recovery with the ORIGINAL q equation, proved by propagation.
   This is not assumed as a geometry/selector hypothesis. -/
theorem RawBlock.recover {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hT : neighborhood M Ω q ⊆ A)
    (hr : 0 < (neighborhood M Ω q).card)
    {a b : Finset X → ℤ} (he : potential M Ω a = potential M Ω b) :
    ∀ v ∈ A ∪ B, a v = b v := by
  obtain ⟨t,ht⟩ := card_pos.mp hr
  let delta : Finset X → ℤ := fun v => a v - b v
  let sign : Finset X → ℤ := fun v => if v ∈ A then 1 else -1
  have edge {s v : Finset X} (hs : s ∈ A ∪ B)
      (hsv : OrdinaryAdj M Ω q s v) : delta s + delta v = 0 := by
    obtain ⟨x,hx⟩ := (h.step hs hsv).2.2
    have hx' := congrFun he x
    rw [potential_pair a hsv.2.2.1 hx, potential_pair b hsv.2.2.1 hx] at hx'
    dsimp [delta]
    omega
  have propagate {v : Finset X}
      (hp : Relation.ReflTransGen (OrdinaryAdj M Ω q) t v) :
      v ∈ A ∪ B ∧ delta v = sign v * delta t := by
    induction hp with
    | refl => exact ⟨mem_union_left _ (hT ht), by simp [sign,hT ht]⟩
    | @tail v w hp hvw ih =>
      have hw := h.step ih.1 hvw
      refine ⟨hw.1,?_⟩
      have hed := edge ih.1 hvw
      have ihv := ih.2
      rcases hw.2.1 with hAB | hBA
      · have hwA : w ∉ A := fun hh => Finset.disjoint_left.mp h.disjoint hh hAB.2
        simp only [sign, if_pos hAB.1, if_neg hwA, one_mul, neg_one_mul] at ihv ⊢
        omega
      · have hvA : v ∉ A := fun hh => Finset.disjoint_left.mp h.disjoint hh hBA.1
        simp only [sign, if_neg hvA, if_pos hBA.2, one_mul, neg_one_mul] at ihv ⊢
        omega
  have hlocal (v : Finset X) (hv : v ∈ A ∪ B) : delta v = sign v * delta t :=
    (propagate (h.connected t (mem_union_left _ (hT ht)) v hv)).2
  have hq := congrFun he q
  rw [potential_apply, potential_apply] at hq
  have hzero : (∑ v ∈ neighborhood M Ω q, delta v) = 0 := by
    dsimp [delta]
    rw [sum_sub_distrib, hq, sub_self]
  have hsum : (∑ v ∈ neighborhood M Ω q, delta v) =
      ((neighborhood M Ω q).card : ℤ) * delta t := by
    calc
      _ = ∑ _v ∈ neighborhood M Ω q, delta t := by
        apply sum_congr rfl
        intro v hv
        simpa [sign,hT hv] using hlocal v (mem_union_left _ (hT hv))
      _ = _ := by simp [nsmul_eq_mul]
  have hdt : delta t = 0 := by
    have hn : ((neighborhood M Ω q).card : ℤ) ≠ 0 := by exact_mod_cast (by omega : (neighborhood M Ω q).card ≠ 0)
    exact (mul_eq_zero.mp (hsum.symm.trans hzero)).resolve_left hn
  intro v hv
  have hz := hlocal v hv
  dsimp [delta] at hz hdt
  rw [hdt,mul_zero] at hz
  omega

/- A Boolean potential with q=0 and a negative coefficient is impossible.
   Both native test potentials below consume this inference. -/
theorem RawBlock.no_negative_boolean {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hT : neighborhood M Ω q ⊆ A)
    (hr : 0 < (neighborhood M Ω q).card) (hqΩ : q ∈ Ω)
    (a : Finset X → ℤ) (haq : potential M Ω a q = 0)
    (hbool : ∀ x, potential M Ω a x = 0 ∨ potential M Ω a x = 1)
    {v : Finset X} (hv : v ∈ A ∪ B) (hneg : a v < 0) : False := by
  have hnz : potential M Ω a ≠ 0 := by
    intro he
    have he' : potential M Ω a = potential M Ω (fun _ => 0) := by simpa [potential] using he
    have hv' := h.recover hT hr he' v hv
    omega
  let C := Ω.filter (fun x => potential M Ω a x = 1)
  have hrow : row C = potential M Ω a := by
    ext x
    by_cases hxΩ : x ∈ Ω
    · rcases hbool x with hx | hx <;> simp [row,C,hxΩ,hx]
    · simp [row,C,hxΩ,potential_outside a hxΩ]
  have hCn : C.Nonempty := by
    by_contra hn
    have hz : C = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hnz
    rw [← hrow,hz]
    ext x
    simp [row]
  have hCq : q ∉ C := by simp [C,haq]
  have hC : Complete M Ω C :=
    ⟨filter_subset _ _,hCn,fun he => hCq (he.symm ▸ hqΩ),hrow.symm ▸ potential_mem a⟩
  obtain ⟨Q,hQP,hQI,hcover,hsum⟩ := complete_disjoint_decomposition hC
  have he : potential M Ω a = potential M Ω (fun S => if S ∈ Q then 1 else 0) := by
    rw [potential_selector hQP,← hsum,hrow]
  have hv' := h.recover hT hr he v hv
  by_cases hvQ : v ∈ Q <;> simp [hvQ] at hv' <;> omega

/- Find the genuine original endpoints of a coordinate in a supported
   potential; outside coordinates contribute zero, including unused IDs. -/
private theorem RawBlock.supported_value {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (a : Finset X → ℤ)
    (hsupp : ∀ v, v ∉ A ∪ B → a v = 0) {x : X} (hxq : x ≠ q) :
    potential M Ω a x = 0 ∨
      ∃ s ∈ A, ∃ t ∈ B, neighborhood M Ω x = {s,t} ∧
        x ∈ s ∧ x ∈ t ∧ potential M Ω a x = a s + a t := by
  by_cases hz : ∀ v ∈ neighborhood M Ω x, a v = 0
  · left
    rw [potential_apply]
    exact sum_eq_zero hz
  · push_neg at hz
    obtain ⟨v,hv,hvn⟩ := hz
    have hvJ : v ∈ A ∪ B := by
      by_contra hn
      exact hvn (hsupp v hn)
    obtain ⟨s,hs,t,ht,hN⟩ := h.port v hvJ x (mem_neighborhood.mp hv).2 hxq
    have hxs : x ∈ s := (mem_neighborhood.mp (hN.symm ▸ (by simp : s ∈ ({s,t} : Finset (Finset X))))).2
    have hxt : x ∈ t := (mem_neighborhood.mp (hN.symm ▸ (by simp : t ∈ ({s,t} : Finset (Finset X))))).2
    exact Or.inr ⟨s,hs,t,ht,hN,hxs,hxt,potential_pair a (h.left_ne_right hs ht) hN⟩

private theorem RawBlock.adj_pair {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) {a b : Finset X} (ha : a ∈ A) (hb : b ∈ B)
    {x : X} (hxq : x ≠ q) (hxa : x ∈ a) (hxb : x ∈ b) :
    OrdinaryAdj M Ω q a b :=
  ⟨h.left_minimal ha,h.right_minimal hb,h.left_ne_right ha hb,x,hxq,hxa,hxb⟩

def deleteTest (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (v w : Finset X) : ℤ :=
  -(if w = v then 1 else 0) + (if OrdinaryAdj M Ω q v w then 1 else 0)

private theorem RawBlock.deleteTest_supported {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) {v : Finset X} (hv : v ∈ A) :
    ∀ w, w ∉ A ∪ B → deleteTest M Ω q v w = 0 := by
  intro w hw
  have hwv : w ≠ v := by rintro rfl; exact hw (mem_union_left _ hv)
  have hn : ¬OrdinaryAdj M Ω q v w := fun he => hw (h.step (mem_union_left _ hv) he).1
  simp [deleteTest,hwv,hn]

/-- The first actual native negative test proves A=T. No projected Boolean
family, selector or local injectivity is an input. -/
theorem RawBlock.left_eq_terminals {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hT : neighborhood M Ω q ⊆ A)
    (hr : 0 < (neighborhood M Ω q).card) (hqΩ : q ∈ Ω) :
    A = neighborhood M Ω q := by
  apply Subset.antisymm _ hT
  intro v hv
  by_contra hvT
  let a := deleteTest M Ω q v
  have haq : potential M Ω a q = 0 := by
    rw [potential_apply]
    apply sum_eq_zero
    intro t ht
    have htv : t ≠ v := by rintro rfl; exact hvT ht
    simp [a,deleteTest,htv,h.no_same_left hv (hT ht)]
  have hbool : ∀ x, potential M Ω a x = 0 ∨ potential M Ω a x = 1 := by
    intro x
    by_cases hxq : x = q
    · exact Or.inl (by simpa [hxq] using haq)
    rcases h.supported_value a (h.deleteTest_supported hv) hxq with hz |
      ⟨s,hs,t,ht,hN,hxs,hxt,he⟩
    · exact Or.inl hz
    have htv : t ≠ v := (h.left_ne_right hv ht).symm
    have hvs : ¬OrdinaryAdj M Ω q v s := h.no_same_left hv hs
    by_cases hsv : s = v
    · subst s
      have hadj := h.adj_pair hv ht hxq hxs hxt
      left
      simpa [a,deleteTest,htv,hadj,hvs] using he
    · by_cases hadj : OrdinaryAdj M Ω q v t
      · right
        simpa [a,deleteTest,hsv,htv,hadj,hvs] using he
      · left
        simpa [a,deleteTest,hsv,htv,hadj,hvs] using he
  have hself : ¬OrdinaryAdj M Ω q v v := fun hh => hh.2.2.1 rfl
  exact h.no_negative_boolean hT hr hqΩ a haq hbool (mem_union_left _ hv)
    (by simp [a,deleteTest,hself])

def pairTest (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (t s w : Finset X) : ℤ :=
  -(if w = t then 1 else 0) + (if w = s then 1 else 0) +
    (if OrdinaryAdj M Ω q t w then 1 else 0)

/-- The second actual native negative test proves every terminal pair has an
ordinary common neighbour in B. It uses all Complete rows via the quotient
adapter, including larger rows and unions in other components. -/
theorem RawBlock.common_neighbour {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hA : A = neighborhood M Ω q)
    (hr : 0 < (neighborhood M Ω q).card) (hqΩ : q ∈ Ω)
    {t s : Finset X} (ht : t ∈ neighborhood M Ω q)
    (hs : s ∈ neighborhood M Ω q) (hts : t ≠ s) :
    ∃ b ∈ B, OrdinaryAdj M Ω q t b ∧ OrdinaryAdj M Ω q s b := by
  by_contra hno
  have htA : t ∈ A := hA.symm ▸ ht
  have hsA : s ∈ A := hA.symm ▸ hs
  have hT : neighborhood M Ω q ⊆ A := by rw [hA]
  let a := pairTest M Ω q t s
  have hsupp : ∀ w, w ∉ A ∪ B → a w = 0 := by
    intro w hw
    have hwt : w ≠ t := by rintro rfl; exact hw (mem_union_left _ htA)
    have hws : w ≠ s := by rintro rfl; exact hw (mem_union_left _ hsA)
    have hn : ¬OrdinaryAdj M Ω q t w := fun he => hw (h.step (mem_union_left _ htA) he).1
    simp [a,pairTest,hwt,hws,hn]
  have haq : potential M Ω a q = 0 := by
    rw [potential_apply]
    have he : ∀ w ∈ neighborhood M Ω q,
        a w = -(if w = t then 1 else 0) + (if w = s then 1 else 0) := by
      intro w hw
      simp [a,pairTest,h.no_same_left htA (hT hw)]
    rw [sum_congr rfl he, sum_add_distrib]
    simp [ht,hs]
  have hbool : ∀ x, potential M Ω a x = 0 ∨ potential M Ω a x = 1 := by
    intro x
    by_cases hxq : x = q
    · exact Or.inl (by simpa [hxq] using haq)
    rcases h.supported_value a hsupp hxq with hz |
      ⟨v,hv,b,hb,hN,hxv,hxb,he⟩
    · exact Or.inl hz
    have hbt : b ≠ t := (h.left_ne_right htA hb).symm
    have hbs : b ≠ s := (h.left_ne_right hsA hb).symm
    have htv : ¬OrdinaryAdj M Ω q t v := h.no_same_left htA hv
    by_cases hvt : v = t
    · subst v
      have htb := h.adj_pair htA hb hxq hxv hxb
      left
      simpa [a,pairTest,hbt,hbs,hts,htb,htv] using he
    · by_cases hvs : v = s
      · subst v
        have hsb := h.adj_pair hsA hb hxq hxv hxb
        have htb : ¬OrdinaryAdj M Ω q t b := fun hh => hno ⟨b,hb,hh,hsb⟩
        right
        simpa [a,pairTest,hvt,hbt,hbs,htb,htv] using he
      · by_cases htb : OrdinaryAdj M Ω q t b
        · right
          simpa [a,pairTest,hvt,hvs,hbt,hbs,htb,htv] using he
        · left
          simpa [a,pairTest,hvt,hvs,hbt,hbs,htb,htv] using he
  have hself : ¬OrdinaryAdj M Ω q t t := fun hh => hh.2.2.1 rfl
  exact h.no_negative_boolean hT hr hqΩ a haq hbool (mem_union_left _ htA)
    (by simp [a,pairTest,hts,hself])

private theorem RawBlock.right_port {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hA : A = neighborhood M Ω q)
    {b : Finset X} (hb : b ∈ B) {x : X} (hx : x ∈ b) :
    ∃ t ∈ neighborhood M Ω q, x ∈ t ∧ neighborhood M Ω x = {t,b} := by
  have hT : neighborhood M Ω q ⊆ A := by rw [hA]
  have hxq : x ≠ q := by rintro rfl; exact h.no_q_right hT hb hx
  obtain ⟨t,ht,c,hc,hN⟩ := h.port b (mem_union_right _ hb) x hx hxq
  have hbN : b ∈ ({t,c} : Finset (Finset X)) := by
    rw [← hN]
    exact mem_neighborhood.mpr ⟨h.right_minimal hb,hx⟩
  have hbc : b = c := by
    rcases mem_insert.mp hbN with he | he
    · exact ((h.left_ne_right ht hb) he.symm).elim
    · exact mem_singleton.mp he
  subst c
  refine ⟨t,hA ▸ ht,?_,hN⟩
  exact (mem_neighborhood.mp (hN.symm ▸ (by simp : t ∈ ({t,b} : Finset (Finset X))))).2

/-- Every opposite original row has at least two DISTINCT terminal neighbours.
This comes from actual inclusion minimality, not an assumed graph degree. -/
theorem RawBlock.right_degree {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hA : A = neighborhood M Ω q)
    {b : Finset X} (hb : b ∈ B) :
    2 ≤ (terminalNeighbors M Ω q b).card := by
  have hT : neighborhood M Ω q ⊆ A := by rw [hA]
  obtain ⟨x,hx⟩ := (mem_minimalFamily.mp (h.right_minimal hb)).2.1.2.1
  obtain ⟨t,ht,hxt,hN⟩ := h.right_port hA hb hx
  have htn : t ∈ terminalNeighbors M Ω q b :=
    mem_terminalNeighbors.mpr ⟨ht,x,mem_inter.mpr ⟨hx,hxt⟩⟩
  by_contra hsmall
  have hall : ∀ s ∈ terminalNeighbors M Ω q b, s = t := by
    intro s hs
    by_contra hst
    have htwo := Finset.one_lt_card.mpr ⟨s,hs,t,htn,hst⟩
    omega
  have hbt : b ⊆ t := by
    intro y hy
    obtain ⟨s,hs,hys,_⟩ := h.right_port hA hb hy
    have hsn : s ∈ terminalNeighbors M Ω q b :=
      mem_terminalNeighbors.mpr ⟨hs,y,mem_inter.mpr ⟨hy,hys⟩⟩
    exact hall s hsn ▸ hys
  have htm := (mem_minimalFamily.mp (mem_neighborhood.mp ht).1).2
  have hbm := (mem_minimalFamily.mp (h.right_minimal hb)).2
  have he : b = t := htm.2 b hbm.1 hbt
  exact h.no_q_right hT hb (he.symm ▸ (mem_neighborhood.mp ht).2)

private theorem terminal_has_port (hr : 2 ≤ (neighborhood M Ω q).card)
    {t : Finset X} (ht : t ∈ neighborhood M Ω q) :
    ∃ x ∈ t, x ≠ q := by
  by_contra hn
  have hsub : t ⊆ {q} := by
    intro x hx
    by_contra hxq
    exact hn ⟨x,hx,by simpa using hxq⟩
  obtain ⟨s,hs,hst⟩ := Finset.exists_mem_ne (by omega : 1 < (neighborhood M Ω q).card) t
  have hts : t ⊆ s := fun x hx => by
    have hxq : x = q := mem_singleton.mp (hsub hx)
    exact hxq.symm ▸ (mem_neighborhood.mp hs).2
  have hsM := (mem_minimalFamily.mp (mem_neighborhood.mp hs).1).2
  have htC := (mem_minimalFamily.mp (mem_neighborhood.mp ht).1).2.1
  exact hst (hsM.2 t htC hts).symm

theorem RawBlock.right_nonempty {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) (hA : A = neighborhood M Ω q)
    (hr : 2 ≤ (neighborhood M Ω q).card) : B.Nonempty := by
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (by omega : 0 < (neighborhood M Ω q).card)
  obtain ⟨x,hxt,hxq⟩ := terminal_has_port hr ht
  obtain ⟨a,ha,b,hb,_⟩ := h.port t (mem_union_left _ (hA.symm ▸ ht)) x hxt hxq
  exact ⟨b,hb⟩

/-- Complete positive geometry, except for the deliberate universal/nonuniversal
case split. All degree, pair-incidence and coverage fields are proved above. -/
theorem positive_charge_incidence
    (hqΩ : q ∈ Ω) (hr : 2 ≤ (neighborhood M Ω q).card)
    (hd : chargeGCD M Ω q = (neighborhood M Ω q).card) :
    ∃ B : Finset (Finset X),
      RawBlock M Ω q (neighborhood M Ω q) B ∧ B.Nonempty ∧
      (∀ b ∈ B, q ∉ b) ∧
      (∀ b ∈ B, 2 ≤ (terminalNeighbors M Ω q b).card) ∧
      (∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q, s ≠ t →
        ∃ b ∈ B, s ∈ terminalNeighbors M Ω q b ∧ t ∈ terminalNeighbors M Ω q b) ∧
      (∀ b ∈ B, ∀ t ∈ neighborhood M Ω q, ∀ x ∈ b, x ∈ t →
        neighborhood M Ω x = {t,b}) := by
  obtain ⟨A,B,hraw,hc⟩ := positive_charge_block (by omega) hd
  have hT := hraw.terminals_left hc
  have hA := hraw.left_eq_terminals hT (by omega) hqΩ
  subst A
  refine ⟨B,hraw,hraw.right_nonempty rfl hr,?_,?_,?_,?_⟩
  · intro b hb
    exact hraw.no_q_right (fun ht => ht) hb
  · intro b hb
    exact hraw.right_degree rfl hb
  · intro s hs t ht hst
    obtain ⟨b,hb,hsb,htb⟩ := hraw.common_neighbour rfl (by omega) hqΩ hs ht hst
    obtain ⟨x,hxq,hxs,hxb⟩ := hsb.2.2.2
    obtain ⟨y,hyq,hyt,hyb⟩ := htb.2.2.2
    exact ⟨b,hb,mem_terminalNeighbors.mpr ⟨hs,x,mem_inter.mpr ⟨hxb,hxs⟩⟩,
      mem_terminalNeighbors.mpr ⟨ht,y,mem_inter.mpr ⟨hyb,hyt⟩⟩⟩
  · intro b hb t ht x hxb hxt
    obtain ⟨s,hs,hxs,hN⟩ := hraw.right_port rfl hb hxb
    have htN : t ∈ ({s,b} : Finset (Finset X)) := by
      rw [← hN]
      exact mem_neighborhood.mpr ⟨(mem_neighborhood.mp ht).1,hxt⟩
    have hts : t = s := by
      rcases mem_insert.mp htN with he | he
      · exact he
      · have htb : t = b := mem_singleton.mp he
        exact ((hraw.left_ne_right ht hb) htb).elim
    simpa [hts] using hN

/- A bounded finite rank with chosen endpoints; no total-order or rank data
   is imposed on the original system. -/
theorem exists_endpoint_rank (T : Finset (Finset X)) {a z : Finset X}
    (ha : a ∈ T) (hz : z ∈ T) (haz : a ≠ z) :
    ∃ rank : Finset X → ℕ,
      (∀ s ∈ T, ∀ t ∈ T, rank s = rank t → s = t) ∧
      (∀ t ∈ T, rank a ≤ rank t) ∧
      (∀ t ∈ T, rank t ≤ rank z) := by
  let rank : Finset X → ℕ := fun t =>
    if t = a then 0 else if t = z then T.card + 1 else 1 + T.toList.idxOf t
  have hra : rank a = 0 := by simp [rank]
  have hrz : rank z = T.card + 1 := by simp [rank,haz.symm]
  have middle {t : Finset X} (ht : t ∈ T) (hta : t ≠ a) (htz : t ≠ z) :
      0 < rank t ∧ rank t < T.card + 1 := by
    have hi := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr ht)
    simp only [Finset.length_toList] at hi
    simp only [rank,if_neg hta,if_neg htz]
    omega
  refine ⟨rank,?_,?_,?_⟩
  · intro s hs t ht he
    by_cases hsa : s = a
    · subst s
      by_cases hta : t = a
      · exact hta.symm
      by_cases htz : t = z
      · subst t
        rw [hra,hrz] at he
        omega
      · have := middle ht hta htz
        rw [hra] at he
        omega
    by_cases hsz : s = z
    · subst s
      by_cases hta : t = a
      · subst t
        rw [hra,hrz] at he
        omega
      by_cases htz : t = z
      · exact htz.symm
      · have := middle ht hta htz
        rw [hrz] at he
        omega
    by_cases hta : t = a
    · subst t
      have := middle hs hsa hsz
      rw [hra] at he
      omega
    by_cases htz : t = z
    · subst t
      have := middle hs hsa hsz
      rw [hrz] at he
      omega
    have hi : T.toList.idxOf s = T.toList.idxOf t := by
      simp only [rank,if_neg hsa,if_neg hsz,if_neg hta,if_neg htz] at he
      omega
    exact (List.idxOf_inj (Finset.mem_toList.mpr hs)).mp hi
  · intro t ht
    rw [hra]
    exact Nat.zero_le _
  · intro t ht
    rw [hrz]
    by_cases hta : t = a
    · simp [hta,hra]
    by_cases htz : t = z
    · simp [htz,hrz]
    · exact (middle ht hta htz).2.le

/-- The non-universal branch produces actual b0,a,z,u and a finite injective
rank with a first and z last. The universal branch is returned explicitly. -/
theorem positive_geometry_or_universal
    (hqΩ : q ∈ Ω) (hr : 2 ≤ (neighborhood M Ω q).card)
    (hd : chargeGCD M Ω q = (neighborhood M Ω q).card) :
    (∃ B : Finset (Finset X), RawBlock M Ω q (neighborhood M Ω q) B ∧
      ∃ b0 ∈ B, ∀ t ∈ neighborhood M Ω q, t ∈ terminalNeighbors M Ω q b0) ∨
    ∃ (G : Geometry M Ω q) (b0 a z u : Finset X) (rank : Finset X → ℕ),
      RawBlock M Ω q (neighborhood M Ω q) G.B ∧
      b0 ∈ G.B ∧ a ∈ terminalNeighbors M Ω q b0 ∧
      z ∈ terminalNeighbors M Ω q b0 ∧ a ≠ z ∧
      u ∈ neighborhood M Ω q ∧ u ∉ terminalNeighbors M Ω q b0 ∧
      (∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
        rank s = rank t → s = t) ∧
      (∀ t ∈ neighborhood M Ω q, rank a ≤ rank t) ∧
      (∀ t ∈ neighborhood M Ω q, rank t ≤ rank z) := by
  obtain ⟨B,hraw,hBn,hqB,hdeg,hcover,hpair⟩ := positive_charge_incidence hqΩ hr hd
  by_cases huniv : ∃ b0 ∈ B, ∀ t ∈ neighborhood M Ω q,
      t ∈ terminalNeighbors M Ω q b0
  · exact Or.inl ⟨B,hraw,huniv⟩
  · have hno : ∀ b ∈ B, ∃ t ∈ neighborhood M Ω q,
        t ∉ terminalNeighbors M Ω q b := by
      intro b hb
      by_contra hn
      apply huniv
      refine ⟨b,hb,?_⟩
      intro t ht
      by_contra hnt
      exact hn ⟨t,ht,hnt⟩
    let G : Geometry M Ω q :=
      ⟨B,hqΩ,hraw.right_minimal,hqB,hpair,hdeg,hcover,hno⟩
    obtain ⟨b0,hb0⟩ := hBn
    obtain ⟨a,ha,z,hz,haz⟩ := one_lt_card.mp
      (show 1 < (terminalNeighbors M Ω q b0).card by have := hdeg b0 hb0; omega)
    obtain ⟨u,hu,hu0⟩ := hno b0 hb0
    obtain ⟨rank,hrank,hmin,hmax⟩ := exists_endpoint_rank (neighborhood M Ω q)
      (mem_terminalNeighbors.mp ha).1 (mem_terminalNeighbors.mp hz).1 haz
    exact Or.inr ⟨G,b0,a,z,u,rank,hraw,hb0,ha,hz,haz,hu,hu0,hrank,hmin,hmax⟩

/- Identification with the actual ordinary-component definition of d.
The bound on EVERY non-q original incidence is used here, not replaced
by a bound on a projected/scaled family. -/

structure ComponentSides (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (A B : Finset (Finset X)) : Prop where
  left_minimal : A ⊆ minimalFamily M Ω
  right_minimal : B ⊆ minimalFamily M Ω
  disjoint : Disjoint A B
  nonempty : (A ∪ B).Nonempty
  connected : ∀ s ∈ A ∪ B, ∀ t ∈ A ∪ B,
    Relation.ReflTransGen (OrdinaryAdj M Ω q) s t
  closed : ∀ s ∈ A ∪ B, ∀ t, OrdinaryAdj M Ω q s t → t ∈ A ∪ B
  ungrounded : ∀ v ∈ A ∪ B, ∀ x ∈ v, x ≠ q → 2 ≤ (neighborhood M Ω x).card
  no_left_edge : ∀ s ∈ A, ∀ t ∈ A, ¬OrdinaryAdj M Ω q s t
  no_right_edge : ∀ s ∈ B, ∀ t ∈ B, ¬OrdinaryAdj M Ω q s t

theorem RawBlock.componentSides {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) : ComponentSides M Ω q A B := by
  refine ⟨h.left_minimal,h.right_minimal,h.disjoint,h.nonempty,h.connected,?_,?_,?_,?_⟩
  · intro s hs t hst
    exact (h.step hs hst).1
  · intro v hv x hx hxq
    obtain ⟨a,ha,b,hb,hN⟩ := h.port v hv x hx hxq
    rw [hN]
    simp [h.left_ne_right ha hb]
  · intro s hs t ht
    exact h.no_same_left hs ht
  · intro s hs t ht
    exact h.swap.no_same_left hs ht

theorem ComponentSides.rawBlock
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2)
    {A B : Finset (Finset X)} (h : ComponentSides M Ω q A B) :
    RawBlock M Ω q A B := by
  refine ⟨h.left_minimal,h.right_minimal,h.disjoint,h.nonempty,h.connected,?_⟩
  intro v hv x hx hxq
  have hvV : v ∈ minimalFamily M Ω := by
    rcases mem_union.mp hv with hv | hv
    · exact h.left_minimal hv
    · exact h.right_minimal hv
  have hvN : v ∈ neighborhood M Ω x := mem_neighborhood.mpr ⟨hvV,hx⟩
  obtain ⟨w,hwN,hwv⟩ := Finset.exists_mem_ne (s := neighborhood M Ω x)
    (by have := h.ungrounded v hv x hx hxq; omega) v
  have hw := mem_neighborhood.mp hwN
  have hadj : OrdinaryAdj M Ω q v w := ⟨hvV,hw.1,hwv.symm,x,hxq,hx,hw.2⟩
  have hwJ := h.closed v hv w hadj
  have hsub : ({v,w} : Finset (Finset X)) ⊆ neighborhood M Ω x := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact hvN
    · exact (mem_singleton.mp ht).symm ▸ hwN
  have hN : neighborhood M Ω x = {v,w} := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    simpa [hwv.symm] using hinc x hxq
  rcases mem_union.mp hv with hvA | hvB
  · have hwB : w ∈ B := by
      rcases mem_union.mp hwJ with hwA | hwB
      · exact (h.no_left_edge v hvA w hwA hadj).elim
      · exact hwB
    exact ⟨v,hvA,w,hwB,hN⟩
  · have hwA : w ∈ A := by
      rcases mem_union.mp hwJ with hwA | hwB
      · exact hwA
      · exact (h.no_right_edge v hvB w hwB hadj).elim
    exact ⟨w,hwA,v,hvB,by simpa [Finset.pair_comm] using hN⟩

/-- Actual finite signed-charge inventory of connected ungrounded bipartite
ordinary components, with the two orientations retained. -/
def ordinaryComponentInventory (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X) :
    Finset (Finset (Finset X) × Finset (Finset X)) :=
  ((minimalFamily M Ω).powerset ×ˢ (minimalFamily M Ω).powerset).filter
    (fun p => ComponentSides M Ω q p.1 p.2)

def ordinaryChargeGCD (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X) : ℕ :=
  (ordinaryComponentInventory M Ω q).gcd
    (fun p => (signedCharge M Ω q p.1 p.2).natAbs)

theorem actual_charge_eq
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2) :
    ordinaryChargeGCD M Ω q = chargeGCD M Ω q := by
  have hinv : ordinaryComponentInventory M Ω q = blockInventory M Ω q := by
    ext p
    simp only [ordinaryComponentInventory,blockInventory,mem_filter]
    constructor
    · intro hp
      exact ⟨hp.1,ComponentSides.rawBlock hinc hp.2⟩
    · intro hp
      exact ⟨hp.1,hp.2.componentSides⟩
  simp only [ordinaryChargeGCD,chargeGCD,hinv]

/-- Original positive-charge geometry inference with actual ordinary-component
gcd and the original all-minimal incidence bound as premises. Its conclusion
contains no assumed selector, recovery map, pair coverage, endpoints or rank. -/
theorem original_positive_geometry
    (hqΩ : q ∈ Ω) (hr : 2 ≤ (neighborhood M Ω q).card)
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2)
    (hd : ordinaryChargeGCD M Ω q = (neighborhood M Ω q).card) :
    (∃ B : Finset (Finset X), RawBlock M Ω q (neighborhood M Ω q) B ∧
      ∃ b0 ∈ B, ∀ t ∈ neighborhood M Ω q, t ∈ terminalNeighbors M Ω q b0) ∨
    ∃ (G : Geometry M Ω q) (b0 a z u : Finset X) (rank : Finset X → ℕ),
      RawBlock M Ω q (neighborhood M Ω q) G.B ∧
      b0 ∈ G.B ∧ a ∈ terminalNeighbors M Ω q b0 ∧
      z ∈ terminalNeighbors M Ω q b0 ∧ a ≠ z ∧
      u ∈ neighborhood M Ω q ∧ u ∉ terminalNeighbors M Ω q b0 ∧
      (∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
        rank s = rank t → s = t) ∧
      (∀ t ∈ neighborhood M Ω q, rank a ≤ rank t) ∧
      (∀ t ∈ neighborhood M Ω q, rank t ≤ rank z) := by
  apply positive_geometry_or_universal hqΩ hr
  rwa [← actual_charge_eq hinc]

/- Exact connection to the existing native_avoiding_word: decomposition is
now discharged and all endpoint/rank/geometry data can be obtained above.
Exterior mixed colouring remains an explicitly stated separate obligation;
this consumer is not claimed as a closed positiveGood theorem. -/
theorem nonuniversal_word_consumer (H : Finset (Finset X))
    (G : Geometry (originalSpan H) Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors (originalSpan H) Ω q b0)
    (hz : z ∈ terminalNeighbors (originalSpan H) Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood (originalSpan H) Ω q)
    (hu0 : u ∉ terminalNeighbors (originalSpan H) Ω q b0)
    (hrank : ∀ s ∈ neighborhood (originalSpan H) Ω q,
      ∀ t ∈ neighborhood (originalSpan H) Ω q, rank s = rank t → s = t)
    (hmin : ∀ t ∈ neighborhood (originalSpan H) Ω q, rank a ≤ rank t)
    (hmax : ∀ t ∈ neighborhood (originalSpan H) Ω q, rank t ≤ rank z)
    {K : Finset X} (hK : K ⊆ Ω.erase q) (hKB : ∀ b ∈ G.B, Disjoint K b)
    (houtside : ∀ S ∈ minimalFamily (originalSpan H) Ω, q ∉ S → S ∉ G.B →
      (∃ x ∈ S, x ∈ red G b0 z rank K) ∧
        (∃ y ∈ S, y ∈ blue G b0 z rank K)) :
    ∃ w : List X, w.Perm Ω.toList ∧
      ∀ t : List X, t <:+: w → ¬Complete (originalSpan H) Ω t.toFinset := by
  obtain ⟨C,alpha,beta,hαa,hαR,hβR,hαβ,hw⟩ := native_avoiding_word H G b0 a z u
    rank hb0 ha hz haz hu hu0 hrank hmin hmax hK hKB houtside
    (fun A hA => by
      obtain ⟨Q,hQP,hQI,hcover,_⟩ := complete_disjoint_decomposition hA
      exact ⟨Q,hQP,hQI,hcover⟩)
  exact ⟨cycleWord Ω (blue G b0 z rank K) q alpha beta
    ((C.first :: C.tail).map Prod.snd),hw⟩

/-- Coefficient-ONE original primitive failure, with no saturation. -/
def NoPrimitive (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) : Prop :=
  (∀ i ∈ Ω, (Pi.single i (1 : ℤ) : X → ℤ) ∉ M) ∧
  ∀ i ∈ Ω, ∀ j ∈ Ω, i ≠ j →
    (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ) : X → ℤ) ∉ M

theorem minimal_card_ge_two (hn : NoPrimitive M Ω)
    {S : Finset X} (hS : S ∈ minimalFamily M Ω) : 2 ≤ S.card := by
  have hm := (mem_minimalFamily.mp hS).2
  have hp := hm.1.2.1.card_pos
  by_contra hc
  obtain ⟨i,he⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
  have hiΩ : i ∈ Ω := hm.1.1 (he.symm ▸ (mem_singleton_self i))
  apply hn.1 i hiΩ
  have heq : row S = Pi.single i (1 : ℤ) := by
    rw [he]
    ext x
    simp [row,Pi.single_apply,eq_comm]
  exact heq ▸ hm.1.2.2.2

/-- Intersecting distinct size-two ORIGINAL minimal rows give an actual
unit difference. This excludes the real exterior degree-two obstruction. -/
theorem no_intersecting_size_two (hn : NoPrimitive M Ω)
    {S D : Finset X} (hS : S ∈ minimalFamily M Ω) (hD : D ∈ minimalFamily M Ω)
    (hSD : S ≠ D) (hs : S.card = 2) (hd : D.card = 2) : Disjoint S D := by
  apply Finset.disjoint_left.mpr
  intro e heS heD
  have hsc : (S.erase e).card = 1 := by rw [card_erase_of_mem heS,hs]
  have hdc : (D.erase e).card = 1 := by rw [card_erase_of_mem heD,hd]
  obtain ⟨i,hi⟩ := card_eq_one.mp hsc
  obtain ⟨j,hj⟩ := card_eq_one.mp hdc
  have hiS : i ∈ S.erase e := hi.symm ▸ mem_singleton_self i
  have hjD : j ∈ D.erase e := hj.symm ▸ mem_singleton_self j
  have hei : e ≠ i := (mem_erase.mp hiS).1.symm
  have hej : e ≠ j := (mem_erase.mp hjD).1.symm
  have hS' : S = {e,i} := by rw [← insert_erase heS,hi]
  have hD' : D = {e,j} := by rw [← insert_erase heD,hj]
  have hij : i ≠ j := by
    intro he
    apply hSD
    rw [hS',hD',he]
  have hSi := (mem_minimalFamily.mp hS).1 (mem_of_mem_erase hiS)
  have hDj := (mem_minimalFamily.mp hD).1 (mem_of_mem_erase hjD)
  apply hn.2 i hSi j hDj hij
  have hr : row S - row D = (Pi.single i (1 : ℤ) - Pi.single j 1 : X → ℤ) := by
    ext x
    by_cases hxe : x = e <;> by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp_all [row,hS',hD',Pi.single_apply]
  exact hr ▸ M.sub_mem (mem_minimalFamily.mp hS).2.1.2.2.2
    (mem_minimalFamily.mp hD).2.1.2.2.2

/- Actual TwoColours encoding. Each private original ID gets its OWN free
leaf. Unused IDs never enter the colouring problem; they are later restored
in the all-Ω word by the existing endpoint. Parallel IDs remain distinct. -/
namespace ExteriorEncoding
open D5.S3.Combinatorics.Graph.EdgeColouring

variable (P : Finset (Finset X))

def ids : Finset X := P.biUnion id
abbrev Edge := {x : X // x ∈ ids P}
abbrev Vertex := {S : Finset X // S ∈ P} ⊕ Edge P

def incident (e : Edge P) : Finset (Finset X) := P.filter (fun S => e.val ∈ S)

private theorem incident_nonempty (e : Edge P) : (incident P e).Nonempty := by
  obtain ⟨S,hS,hxS⟩ := mem_biUnion.mp e.property
  exact ⟨S,mem_filter.mpr ⟨hS,hxS⟩⟩

def first (e : Edge P) : Finset X := Classical.choose (incident_nonempty P e)

private theorem first_mem (e : Edge P) : first P e ∈ incident P e :=
  Classical.choose_spec (incident_nonempty P e)

def HasSecond (e : Edge P) : Prop := ∃ S ∈ incident P e, S ≠ first P e

def second (e : Edge P) (h : HasSecond P e) : Finset X := Classical.choose h

private theorem second_mem (e : Edge P) (h : HasSecond P e) :
    second P e h ∈ incident P e ∧ second P e h ≠ first P e := Classical.choose_spec h

def left (e : Edge P) : Vertex P :=
  Sum.inl ⟨first P e,(mem_filter.mp (first_mem P e)).1⟩

def right (e : Edge P) : Vertex P :=
  if h : HasSecond P e then Sum.inl ⟨second P e h,(mem_filter.mp (second_mem P e h).1).1⟩
  else Sum.inr e

theorem loopless (e : Edge P) : left P e ≠ right P e := by
  unfold left right
  split_ifs with h
  · intro he
    have hv := congrArg Subtype.val (Sum.inl.inj he)
    exact (second_mem P e h).2 hv.symm
  · simp

theorem endpoints
    (hinc : ∀ x, ((P.filter (fun S => x ∈ S))).card ≤ 2)
    (e : Edge P) (S : {S : Finset X // S ∈ P}) :
    left P e = Sum.inl S ∨ right P e = Sum.inl S ↔ e.val ∈ S.val := by
  have hfirst := mem_filter.mp (first_mem P e)
  have hSinc : S.val ∈ incident P e ↔ e.val ∈ S.val := by
    simp [incident,S.property]
  by_cases h : HasSecond P e
  · have hsecond := second_mem P e h
    have hsub : ({first P e,second P e h} : Finset (Finset X)) ⊆ incident P e := by
      intro D hD
      rcases mem_insert.mp hD with rfl | hD
      · exact first_mem P e
      · exact (mem_singleton.mp hD).symm ▸ hsecond.1
    have heq : incident P e = {first P e,second P e h} := by
      apply (eq_of_subset_of_card_le hsub ?_).symm
      simpa [hsecond.2.symm] using hinc e.val
    rw [← hSinc,heq]
    simp [left,right,h,Subtype.ext_iff,eq_comm]
  · have hall : ∀ D ∈ incident P e, D = first P e := by
      intro D hD
      by_contra hn
      exact h ⟨D,hD,hn⟩
    constructor
    · rintro (he | he)
      · have hv : first P e = S.val := congrArg Subtype.val (Sum.inl.inj he)
        exact hv ▸ hfirst.2
      · simp [right,h] at he
    · intro hx
      left
      apply congrArg Sum.inl
      apply Subtype.ext
      exact (hall S.val (hSinc.mpr hx)).symm

def constrained : Finset (Vertex P) := Finset.univ.image Sum.inl

private theorem constrained_iff (v : Vertex P) :
    v ∈ constrained P ↔ ∃ S, v = Sum.inl S := by
  simp [constrained,eq_comm]

theorem star_card
    (hinc : ∀ x, ((P.filter (fun S => x ∈ S))).card ≤ 2)
    (S : {S : Finset X // S ∈ P}) :
    (TwoColours.star (left P) (right P) (Sum.inl S)).card = S.val.card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    apply (endpoints P hinc e S).mp
    simpa [TwoColours.star] using he
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro x hx
    have hxE : x ∈ ids P := mem_biUnion.mpr ⟨S.val,S.property,hx⟩
    exact ⟨⟨x,hxE⟩,by simpa [TwoColours.star] using (endpoints P hinc ⟨x,hxE⟩ S).mpr hx,rfl⟩

/-- The actual odd obstruction is excluded by a coefficient-one two-row
certificate, through the caller's no-intersecting-size-two consequence.
There is no assumed no-odd-component argument. -/
theorem no_odd_component
    (hinc : ∀ x, ((P.filter (fun S => x ∈ S))).card ≤ 2)
    (htwo : ∀ S ∈ P, ∀ D ∈ P, S ≠ D → S.card = 2 → D.card = 2 → Disjoint S D) :
    ¬TwoColours.OddComponent (left P) (right P) (constrained P) := by
  rintro ⟨v,hcomp,hodd⟩
  have hv := hcomp v (.refl v)
  obtain ⟨S,hvS⟩ := (constrained_iff P v).mp hv.1
  subst v
  have hs : S.val.card = 2 := by
    rw [← star_card P hinc S]
    exact hv.2
  obtain ⟨e,he⟩ := Finset.card_pos.mp
    (show 0 < (TwoColours.star (left P) (right P) (Sum.inl S)).card by rw [hv.2]; omega)
  have heends : left P e = Sum.inl S ∨ right P e = Sum.inl S := by
    simpa [TwoColours.star] using he
  have hboth : ∃ w : Vertex P, TwoColours.Reach (left P) (right P) (Sum.inl S) w ∧
      w ≠ Sum.inl S ∧ e ∈ TwoColours.star (left P) (right P) w := by
    rcases heends with hel | her
    · refine ⟨right P e,?_,?_,by simp [TwoColours.star]⟩
      · rw [← hel]
        exact .rel _ _ ⟨e,rfl,rfl⟩
      · simpa [hel] using (loopless P e).symm
    · refine ⟨left P e,?_,?_,by simp [TwoColours.star]⟩
      · rw [← her]
        exact .symm _ _ (.rel _ _ ⟨e,rfl,rfl⟩)
      · simpa [her] using loopless P e
  obtain ⟨w,hwReach,hwS,hew⟩ := hboth
  have hw := hcomp w hwReach
  obtain ⟨D,hwD⟩ := (constrained_iff P w).mp hw.1
  subst w
  have hd : D.val.card = 2 := by rw [← star_card P hinc D]; exact hw.2
  have hSD : S.val ≠ D.val := by
    intro heq
    exact hwS (congrArg Sum.inl (Subtype.ext heq.symm))
  have heS := (endpoints P hinc e S).mp heends
  have heD := (endpoints P hinc e D).mp (by simpa [TwoColours.star] using hew)
  exact Finset.disjoint_left.mp (htwo S.val S.property D.val D.property hSD hs hd) heS heD

/-- Actual mixed colouring of original finite rows. Private free leaves and
original ID multiplicity are represented by the concrete endpoints above. -/
theorem mixed_original_rows
    (hinc : ∀ x, ((P.filter (fun S => x ∈ S))).card ≤ 2)
    (hdeg : ∀ S ∈ P, 2 ≤ S.card)
    (htwo : ∀ S ∈ P, ∀ D ∈ P, S ≠ D → S.card = 2 → D.card = 2 → Disjoint S D) :
    ∃ K : Finset X, K ⊆ ids P ∧ ∀ S ∈ P,
      (∃ x ∈ S, x ∉ K) ∧ (∃ y ∈ S, y ∈ K) := by
  have hdeg' : ∀ v ∈ constrained P, 2 ≤ (TwoColours.star (left P) (right P) v).card := by
    intro v hv
    obtain ⟨S,rfl⟩ := (constrained_iff P v).mp hv
    rw [star_card P hinc]
    exact hdeg S.val S.property
  obtain ⟨c,hc⟩ := (TwoColours.exists_iff_no_odd_component (left P) (right P) (constrained P)
    (loopless P) hdeg').mpr (no_odd_component P hinc htwo)
  let K := (ids P).filter (fun x => ∃ hx : x ∈ ids P, c ⟨x,hx⟩ = true)
  have hK (e : Edge P) : e.val ∈ K ↔ c e = true := by simp [K]
  refine ⟨K,filter_subset _ _,?_⟩
  intro S hS
  let v : {S : Finset X // S ∈ P} := ⟨S,hS⟩
  obtain ⟨e,he,f,hf,hef⟩ := hc (Sum.inl v) (by simp [constrained])
  have heS := (endpoints P hinc e v).mp (by simpa [TwoColours.star] using he)
  have hfS := (endpoints P hinc f v).mp (by simpa [TwoColours.star] using hf)
  cases hec : c e <;> cases hfc : c f
  · exact (hef (hec.trans hfc.symm)).elim
  · exact ⟨⟨e.val,heS,by rw [hK]; simp [hec]⟩,
      f.val,hfS,(hK f).mpr hfc⟩
  · exact ⟨⟨f.val,hfS,by rw [hK]; simp [hfc]⟩,
      e.val,heS,(hK e).mpr hec⟩
  · exact (hef (hec.trans hfc.symm)).elim

end ExteriorEncoding

def exteriorFamily (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (B : Finset (Finset X)) : Finset (Finset X) :=
  minimalFamily M Ω \ (neighborhood M Ω q ∪ B)

private theorem exterior_no_q {B : Finset (Finset X)} {S : Finset X}
    (hS : S ∈ exteriorFamily M Ω q B) : q ∉ S := by
  intro hqS
  have hm := mem_sdiff.mp hS
  exact hm.2 (mem_union_left _ (mem_neighborhood.mpr ⟨hm.1,hqS⟩))

/-- Original component closure rules out every shared coordinate with an
exterior original row, including every possible extra supplier of a port. -/
theorem RawBlock.exterior_disjoint {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    {S D : Finset X} (hS : S ∈ exteriorFamily M Ω q B)
    (hD : D ∈ neighborhood M Ω q ∪ B) : Disjoint S D := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxD
  have hxq : x ≠ q := by rintro rfl; exact exterior_no_q hS hxS
  obtain ⟨a,ha,b,hb,hN⟩ := h.port D hD x hxD hxq
  have hSN : S ∈ ({a,b} : Finset (Finset X)) := by
    rw [← hN]
    exact mem_neighborhood.mpr ⟨(mem_sdiff.mp hS).1,hxS⟩
  have hSJ : S ∈ neighborhood M Ω q ∪ B := by
    rcases mem_insert.mp hSN with he | he
    · exact he.symm ▸ mem_union_left _ ha
    · exact (mem_singleton.mp he).symm ▸ mem_union_right _ hb
  exact (mem_sdiff.mp hS).2 hSJ

/-- The original exterior construction factored at RawBlock level. The SAME
TwoColours encoding is shared by the universal and non-universal consumers. -/
theorem RawBlock.exterior_colouring {B : Finset (Finset X)}
    (hraw : RawBlock M Ω q (neighborhood M Ω q) B)
    (hn : NoPrimitive M Ω)
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2) :
    ∃ K : Finset X, K ⊆ (exteriorFamily M Ω q B).biUnion id ∧
      K ⊆ Ω.erase q ∧
      (∀ D ∈ neighborhood M Ω q ∪ B, Disjoint K D) ∧
      ∀ S ∈ exteriorFamily M Ω q B,
        (∃ x ∈ S, x ∉ K) ∧ (∃ y ∈ S, y ∈ K) := by
  let P := exteriorFamily M Ω q B
  have hPV : P ⊆ minimalFamily M Ω := Finset.sdiff_subset
  have hPinc : ∀ x, (P.filter (fun S => x ∈ S)).card ≤ 2 := by
    intro x
    by_cases hxq : x = q
    · subst x
      have he : P.filter (fun S => q ∈ S) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro S hS
        exact exterior_no_q hS
      simp [he]
    · apply le_trans (card_le_card ?_) (hinc x hxq)
      intro S hS
      have hm := mem_filter.mp hS
      exact mem_neighborhood.mpr ⟨hPV hm.1,hm.2⟩
  obtain ⟨K,hKP,hmix⟩ := ExteriorEncoding.mixed_original_rows P hPinc
    (fun S hS => minimal_card_ge_two hn (hPV hS))
    (fun S hS D hD hSD hs hd => no_intersecting_size_two hn (hPV hS) (hPV hD) hSD hs hd)
  have hKE {x : X} (hx : x ∈ K) : ∃ S ∈ P, x ∈ S := mem_biUnion.mp (hKP hx)
  have hK : K ⊆ Ω.erase q := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := hKE hx
    have hxΩ := (mem_minimalFamily.mp (hPV hS)).1 hxS
    have hxq : x ≠ q := by rintro rfl; exact exterior_no_q hS hxS
    exact mem_erase.mpr ⟨hxq,hxΩ⟩
  refine ⟨K,hKP,hK,?_,hmix⟩
  intro D hD
  apply Finset.disjoint_left.mpr
  intro x hxK hxD
  obtain ⟨S,hS,hxS⟩ := hKE hxK
  exact Finset.disjoint_left.mp (hraw.exterior_disjoint hS hD) hxS hxD

/-- Existing non-universal exterior consumer, now using the shared RawBlock
construction. No TwoColours proof is duplicated. -/
theorem exterior_mixed_colouring (G : Geometry M Ω q)
    (hraw : RawBlock M Ω q (neighborhood M Ω q) G.B)
    (hn : NoPrimitive M Ω)
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2)
    (b0 z : Finset X) (rank : Finset X → ℕ) :
    ∃ K : Finset X, K ⊆ Ω.erase q ∧
      (∀ b ∈ G.B, Disjoint K b) ∧
      ∀ S ∈ minimalFamily M Ω, q ∉ S → S ∉ G.B →
        (∃ x ∈ S, x ∈ red G b0 z rank K) ∧
          (∃ y ∈ S, y ∈ blue G b0 z rank K) := by
  obtain ⟨K,hKP,hK,hKJ,hmix⟩ := hraw.exterior_colouring hn hinc
  have hKB : ∀ b ∈ G.B, Disjoint K b := fun b hb => hKJ b (mem_union_right _ hb)
  refine ⟨K,hK,hKB,?_⟩
  intro S hS hqS hSB
  have hSP : S ∈ exteriorFamily M Ω q G.B := by
    apply mem_sdiff.mpr
    refine ⟨hS,?_⟩
    intro hmem
    rcases mem_union.mp hmem with hT | hB
    · exact hqS (mem_neighborhood.mp hT).2
    · exact hSB hB
  obtain ⟨⟨r,hrS,hrK⟩,b,hbS,hbK⟩ := hmix S hSP
  have hrΩ := (mem_minimalFamily.mp hS).1 hrS
  have hrq : r ≠ q := by rintro rfl; exact hqS hrS
  have hrL : r ∉ localBlue G b0 z rank := by
    intro hr
    obtain ⟨D,hD,t,ht,hrD,hrt,hcol⟩ := (mem_filter.mp hr).2
    exact Finset.disjoint_left.mp
      (hraw.exterior_disjoint hSP (mem_union_right _ hD)) hrS hrD
  refine ⟨⟨r,hrS,?_⟩,b,hbS,mem_union_right _ hbK⟩
  simp [red,blue,hrΩ,hrq,hrL,hrK]

/-- Actual original positive-charge non-universal branch. The first disjunct
is the Section 5a branch, consumed below by original_universal_word using
actual universal neighbour data; the second is the literal ALL-Ω avoiding word, produced by
the existing native_avoiding_word. All geometry, rank, disjoint decomposition
and exterior colouring inputs of that endpoint have now been discharged.
This intermediate disjunction is consumed by original_positive_charge_target;
no positiveGood or zero-charge theorem is asserted. -/
theorem original_positive_universal_or_word (H : Finset (Finset X))
    (hqΩ : q ∈ Ω) (hr : 2 ≤ (neighborhood (originalSpan H) Ω q).card)
    (hinc : ∀ x, x ≠ q → (neighborhood (originalSpan H) Ω x).card ≤ 2)
    (hd : ordinaryChargeGCD (originalSpan H) Ω q =
      (neighborhood (originalSpan H) Ω q).card)
    (hn : NoPrimitive (originalSpan H) Ω) :
    (∃ B : Finset (Finset X),
      RawBlock (originalSpan H) Ω q (neighborhood (originalSpan H) Ω q) B ∧
      ∃ b0 ∈ B, ∀ t ∈ neighborhood (originalSpan H) Ω q,
        t ∈ terminalNeighbors (originalSpan H) Ω q b0) ∨
    ∃ w : List X, w.Perm Ω.toList ∧
      ∀ t : List X, t <:+: w → ¬Complete (originalSpan H) Ω t.toFinset := by
  rcases original_positive_geometry hqΩ hr hinc hd with huni |
    ⟨G,b0,a,z,u,rank,hraw,hb0,ha,hz,haz,hu,hu0,hrank,hmin,hmax⟩
  · exact Or.inl huni
  · right
    obtain ⟨K,hK,hKB,hout⟩ := exterior_mixed_colouring G hraw hn hinc b0 z rank
    exact nonuniversal_word_consumer H G b0 a z u rank hb0 ha hz haz hu hu0
      hrank hmin hmax hK hKB hout

/- The literal r=2 one-port universal exception is a primitive, never a
scaled relation. It is useful independently of the remaining Section 5a word. -/
theorem two_terminal_one_port_primitive {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    (hr : (neighborhood M Ω q).card = 2)
    {t : Finset X} (ht : t ∈ neighborhood M Ω q)
    {p : X} (hpq : p ≠ q) (htp : t = {q,p}) :
    (Pi.single q (1 : ℤ) - Pi.single p (1 : ℤ) : X → ℤ) ∈ M := by
  obtain ⟨s,hs,hst⟩ := Finset.exists_mem_ne (s := neighborhood M Ω q) (by omega) t
  have hT : neighborhood M Ω q = {t,s} := by
    have hsub : ({t,s} : Finset (Finset X)) ⊆ neighborhood M Ω q := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact ht
      · exact (mem_singleton.mp hv).symm ▸ hs
    exact (eq_of_subset_of_card_le hsub (by simp [hr,hst.symm])).symm
  obtain ⟨b0,hb0⟩ := h.right_nonempty rfl (by omega)
  have full (b : Finset X) (hb : b ∈ B) : terminalNeighbors M Ω q b = neighborhood M Ω q := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    have hd := h.right_degree rfl hb
    omega
  have hpB : ∀ b ∈ B, p ∈ b := by
    intro b hb
    have htn : t ∈ terminalNeighbors M Ω q b := (full b hb).symm ▸ ht
    obtain ⟨x,hx⟩ := (mem_terminalNeighbors.mp htn).2
    have hx' := mem_inter.mp hx
    have hxq : x ≠ q := by rintro rfl; exact h.no_q_right (fun h => h) hb hx'.1
    have hxp : x = p := by
      have hm : x = q ∨ x = p := by simpa [htp] using hx'.2
      exact hm.resolve_left hxq
    exact hxp ▸ hx'.1
  obtain ⟨v,hv,hpv,hpN⟩ := h.right_port rfl hb0 (hpB b0 hb0)
  have hvt : v = t := by
    have htN : t ∈ neighborhood M Ω p := mem_neighborhood.mpr
      ⟨(mem_neighborhood.mp ht).1,by simp [htp]⟩
    rw [hpN] at htN
    rcases mem_insert.mp htN with he | he
    · exact he.symm
    · have htb0 : t = b0 := mem_singleton.mp he
      exact ((h.left_ne_right ht hb0) htb0).elim
  subst v
  have oneB : ∀ b ∈ B, b = b0 := by
    intro b hb
    have hbN : b ∈ neighborhood M Ω p := mem_neighborhood.mpr ⟨h.right_minimal hb,hpB b hb⟩
    rw [hpN] at hbN
    rcases mem_insert.mp hbN with he | he
    · exact ((h.left_ne_right ht hb) he.symm).elim
    · exact mem_singleton.mp he
  have hps : p ∉ s := by
    intro hps
    have hsN : s ∈ neighborhood M Ω p := mem_neighborhood.mpr ⟨(mem_neighborhood.mp hs).1,hps⟩
    rw [hpN] at hsN
    rcases mem_insert.mp hsN with he | he
    · exact hst he
    · exact ((h.left_ne_right hs hb0) (mem_singleton.mp he)).elim
  have hqB := h.no_q_right (fun h => h) hb0
  have equal_else {x : X} (hxq : x ≠ q) (hxp : x ≠ p) : x ∈ s ↔ x ∈ b0 := by
    constructor
    · intro hxs
      obtain ⟨a,ha,b,hb,hN⟩ := h.port s (mem_union_left _ hs) x hxs hxq
      have hxb : x ∈ b := (mem_neighborhood.mp
        (hN.symm ▸ (by simp : b ∈ ({a,b} : Finset (Finset X))))).2
      exact oneB b hb ▸ hxb
    · intro hxb
      obtain ⟨a,ha,hxa,hN⟩ := h.right_port rfl hb0 hxb
      have ha' : a = t ∨ a = s := by simpa [hT] using ha
      rcases ha' with rfl | rfl
      · have he : x = q ∨ x = p := by simpa [htp] using hxa
        exact (he.elim hxq hxp).elim
      · exact hxa
  have hrow : row s - row b0 = (Pi.single q (1 : ℤ) - Pi.single p (1 : ℤ) : X → ℤ) := by
    ext x
    by_cases hxq : x = q
    · subst x
      simp [row,(mem_neighborhood.mp hs).2,hqB,Pi.single_apply,hpq,hpq.symm]
    by_cases hxp : x = p
    · subst x
      simp [row,hps,hpB b0 hb0,Pi.single_apply,hpq,hpq.symm]
    · have he := equal_else hxq hxp
      by_cases hxs : x ∈ s <;> simp_all [row,Pi.single_apply]
  exact hrow ▸ M.sub_mem (mem_minimalFamily.mp (mem_neighborhood.mp hs).1).2.1.2.2.2
    (mem_minimalFamily.mp (h.right_minimal hb0)).2.1.2.2.2

/-- Finite original H ledger for the actual coefficient-one exceptional
primitive. Arbitrary original labels, torsion and total are untouched. -/
theorem two_terminal_one_port_original_ledger (H : Finset (Finset X))
    {B : Finset (Finset X)}
    (h : RawBlock (originalSpan H) Ω q (neighborhood (originalSpan H) Ω q) B)
    (hr : (neighborhood (originalSpan H) Ω q).card = 2)
    {t : Finset X} (ht : t ∈ neighborhood (originalSpan H) Ω q)
    {p : X} (hpq : p ≠ q) (htp : t = {q,p}) :
    ∃ c : Finset X → ℤ,
      (Pi.single q (1 : ℤ) - Pi.single p (1 : ℤ) : X → ℤ) = ∑ h ∈ H, c h • row h := by
  exact original_ledger (two_terminal_one_port_primitive h hr ht hpq htp)

/-- Under actual primitive failure there are two distinct terminals with at
least two non-q ORIGINAL ports. For r≥3, two one-port terminals would already
be intersecting original size-two rows. For r=2, the preceding coefficient-one
exception rules out even one such terminal. This supplies the first genuine
choices required by the remaining universal-neighbour Section 5a word. -/
theorem two_nonleaf_terminals {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    (hr : 2 ≤ (neighborhood M Ω q).card) (hn : NoPrimitive M Ω) :
    ∃ u ∈ neighborhood M Ω q, ∃ v ∈ neighborhood M Ω q,
      u ≠ v ∧ 2 ≤ (u.erase q).card ∧ 2 ≤ (v.erase q).card := by
  let T := neighborhood M Ω q
  let F := T.filter (fun t => 2 ≤ (t.erase q).card)
  have hFT : F ⊆ T := filter_subset _ _
  have bad_size {t : Finset X} (ht : t ∈ T) (htF : t ∉ F) : t.card = 2 := by
    have htV := (mem_neighborhood.mp ht).1
    have hge := minimal_card_ge_two hn htV
    have hq := (mem_neighborhood.mp ht).2
    have hcard := Finset.card_erase_add_one hq
    have hsmall : ¬2 ≤ (t.erase q).card := fun hc => htF (mem_filter.mpr ⟨ht,hc⟩)
    omega
  have hbad : (T \ F).card ≤ 1 := by
    by_contra hb
    obtain ⟨s,hs,t,ht,hst⟩ := one_lt_card.mp (show 1 < (T \ F).card by omega)
    have hs' := mem_sdiff.mp hs
    have ht' := mem_sdiff.mp ht
    have hd := no_intersecting_size_two hn (mem_neighborhood.mp hs'.1).1
      (mem_neighborhood.mp ht'.1).1 hst (bad_size hs'.1 hs'.2) (bad_size ht'.1 ht'.2)
    exact Finset.disjoint_left.mp hd (mem_neighborhood.mp hs'.1).2
      (mem_neighborhood.mp ht'.1).2
  have hcard := Finset.card_sdiff_add_card_eq_card hFT
  have hF : 2 ≤ F.card := by
    by_cases hr2 : T.card = 2
    · have hempty : T \ F = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        have ht' := mem_sdiff.mp ht
        have hq := (mem_neighborhood.mp ht'.1).2
        have hsize := bad_size ht'.1 ht'.2
        obtain ⟨p,hp⟩ := card_eq_one.mp
          (show (t.erase q).card = 1 by rw [card_erase_of_mem hq,hsize])
        have hpE : p ∈ t.erase q := hp.symm ▸ mem_singleton_self p
        have hpq := (mem_erase.mp hpE).1
        have htp : t = {q,p} := by rw [← insert_erase hq,hp]
        have hprim := two_terminal_one_port_primitive h hr2 ht'.1 hpq htp
        have hsub := (mem_minimalFamily.mp (mem_neighborhood.mp ht'.1).1).1
        exact hn.2 q (hsub hq) p (hsub (mem_of_mem_erase hpE)) hpq.symm hprim
      rw [hempty,card_empty] at hcard
      omega
    · change 2 ≤ T.card at hr
      omega
  obtain ⟨u,hu,v,hv,huv⟩ := one_lt_card.mp (show 1 < F.card by omega)
  have hu' := mem_filter.mp hu
  have hv' := mem_filter.mp hv
  exact ⟨u,hu'.1,v,hv'.1,huv,hu'.2,hv'.2⟩

/-- All four distinct original Section 5a frame IDs really exist, including
parallel-port and r=2 cases. Colours and the universal word are not asserted
by this frame theorem. The two_nonleaf_terminals inference is consumed here. -/
theorem universal_original_frame {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    (hr : 2 ≤ (neighborhood M Ω q).card) (hn : NoPrimitive M Ω)
    {b0 : Finset X} (hb0 : b0 ∈ B)
    (huni : ∀ t ∈ neighborhood M Ω q, t ∈ terminalNeighbors M Ω q b0) :
    ∃ u ∈ neighborhood M Ω q, ∃ v ∈ neighborhood M Ω q,
      u ≠ v ∧ ∃ l rho a b : X,
      l ∈ b0 ∩ u ∧ rho ∈ b0 ∩ v ∧ a ∈ u.erase q ∧ b ∈ v.erase q ∧
      a ≠ l ∧ b ≠ rho ∧ [l,rho,a,b].Nodup := by
  obtain ⟨u,hu,v,hv,huv,hud,hvd⟩ := two_nonleaf_terminals h hr hn
  obtain ⟨l,hl⟩ := (mem_terminalNeighbors.mp (huni u hu)).2
  obtain ⟨rho,hrho⟩ := (mem_terminalNeighbors.mp (huni v hv)).2
  obtain ⟨a,ha,hal⟩ := Finset.exists_mem_ne (s := u.erase q) (by omega) l
  obtain ⟨b,hb,hbrho⟩ := Finset.exists_mem_ne (s := v.erase q) (by omega) rho
  have hl' := mem_inter.mp hl
  have hrho' := mem_inter.mp hrho
  have hlq : l ≠ q := by rintro rfl; exact h.no_q_right (fun ht => ht) hb0 hl'.1
  have ha' := mem_erase.mp ha
  have hb' := mem_erase.mp hb
  have across {x y : X} (hx : x ∈ u) (hxq : x ≠ q) (hy : y ∈ v) : x ≠ y := by
    intro he
    apply h.no_same_left hu hv
    exact ⟨(mem_neighborhood.mp hu).1,(mem_neighborhood.mp hv).1,huv,
      x,hxq,hx,he.symm ▸ hy⟩
  have hlrho := across hl'.2 hlq hrho'.2
  have hlb := across hl'.2 hlq hb'.2
  have harho := across ha'.2 ha'.1 hrho'.2
  have hab := across ha'.2 ha'.1 hb'.2
  refine ⟨u,hu,v,hv,huv,l,rho,a,b,hl,hrho,ha,hb,hal,hbrho,?_⟩
  simp [List.nodup_cons,hlrho,hal.symm,hlb,harho.symm,hbrho.symm,hab]

/- Section 5a additions; inserted before the exact target definition. -/

private theorem RawBlock.right_rows_disjoint {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    {D E : Finset X} (hD : D ∈ B) (hE : E ∈ B) (hDE : D ≠ E) : Disjoint D E := by
  apply Finset.disjoint_left.mpr
  intro x hxD hxE
  have hxq : x ≠ q := by rintro rfl; exact h.no_q_right (fun ht => ht) hD hxD
  exact h.swap.no_same_left hD hE
    ⟨h.right_minimal hD,h.right_minimal hE,hDE,x,hxq,hxD,hxE⟩

/-- Extend the two possible prescribed original IDs on a star. Only one blue
ID is needed; the star's second original ID supplies red. -/
private theorem mixed_prescribed_star (S : Finset X) (hS : 2 ≤ S.card)
    (a b : X) (hab : a ≠ b) :
    ∃ C : Finset X, C ⊆ S ∧ b ∉ C ∧ (a ∈ S → a ∈ C) ∧
      (∃ x ∈ S, x ∉ C) ∧ (∃ y ∈ S, y ∈ C) := by
  by_cases ha : a ∈ S
  · obtain ⟨x,hx,hxa⟩ := Finset.exists_mem_ne (s := S) (by omega) a
    exact ⟨{a},by simpa using ha,by simpa using hab.symm,
      fun _ => mem_singleton_self a,⟨x,hx,by simpa using hxa⟩,
      a,ha,mem_singleton_self a⟩
  · obtain ⟨y,hy,hyb⟩ := Finset.exists_mem_ne (s := S) (by omega) b
    obtain ⟨x,hx,hxy⟩ := Finset.exists_mem_ne (s := S) (by omega) y
    exact ⟨{y},by simpa using hy,by simpa using hyb.symm,
      fun haa => (ha haa).elim,⟨x,hx,by simpa using hxy⟩,
      y,hy,mem_singleton_self y⟩

/-- Construct the universal frame colouring on ALL original coordinates.
Every other terminal gets blue on b0. On b0 only l,b are red; a,b may
both lie in b0. The other B stars are coloured independently using their
literal disjoint coordinate sets. The exterior comes from the shared
RawBlock/TwoColours supplier; unused Ω IDs remain red. -/
theorem universal_mixed_colouring {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    (hn : NoPrimitive M Ω)
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2)
    {b0 u v : Finset X} (hb0 : b0 ∈ B)
    (hu : u ∈ neighborhood M Ω q) (hv : v ∈ neighborhood M Ω q)
    (huni : ∀ t ∈ neighborhood M Ω q, t ∈ terminalNeighbors M Ω q b0)
    {l rho a b : X} (hl : l ∈ b0 ∩ u) (hrho : rho ∈ b0 ∩ v)
    (ha : a ∈ u.erase q) (hb : b ∈ v.erase q) (hnd : [l,rho,a,b].Nodup) :
    ∃ Blue : Finset X, Blue ⊆ Ω.erase q ∧
      l ∈ Ω \ insert q Blue ∧ rho ∈ Blue ∧ a ∈ Blue ∧ b ∈ Ω \ insert q Blue ∧
      (∀ t ∈ neighborhood M Ω q, ∃ x ∈ t, x ∈ Blue) ∧
      ∀ S ∈ minimalFamily M Ω, q ∉ S →
        (∃ x ∈ S, x ∈ Ω \ insert q Blue) ∧ (∃ y ∈ S, y ∈ Blue) := by
  have hdist : l ≠ rho ∧ l ≠ a ∧ l ≠ b ∧ rho ≠ a ∧ rho ≠ b ∧ a ≠ b := by
    simpa [List.nodup_cons,and_assoc] using hnd
  obtain ⟨hlrho,hla,hlb,hrhoa,hrhob,hab⟩ := hdist
  have hl' := mem_inter.mp hl
  have hrho' := mem_inter.mp hrho
  have ha' := mem_erase.mp ha
  have hb' := mem_erase.mp hb
  have hlq : l ≠ q := by rintro rfl; exact h.no_q_right (fun ht => ht) hb0 hl'.1
  have hrhoq : rho ≠ q := by rintro rfl; exact h.no_q_right (fun ht => ht) hb0 hrho'.1
  have hlocal : ∀ D ∈ B, ∃ C : Finset X, C ⊆ D ∧ b ∉ C ∧
      (a ∈ D → a ∈ C) ∧ (∃ x ∈ D, x ∉ C) ∧ (∃ y ∈ D, y ∈ C) ∧
      (D = b0 → C = D \ {l,b}) := by
    intro D hD
    by_cases hD0 : D = b0
    · subst D
      refine ⟨b0 \ {l,b},sdiff_subset,?_,?_,?_,?_,fun _ => rfl⟩
      · simp
      · intro ha0
        exact mem_sdiff.mpr ⟨ha0,by simp [hla.symm,hab]⟩
      · exact ⟨l,hl'.1,by simp⟩
      · exact ⟨rho,hrho'.1,mem_sdiff.mpr ⟨hrho'.1,by simp [hlrho.symm,hrhob]⟩⟩
    · obtain ⟨C,hCD,hbC,haC,hred,hblue⟩ :=
        mixed_prescribed_star D (minimal_card_ge_two hn (h.right_minimal hD)) a b hab
      exact ⟨C,hCD,hbC,haC,hred,hblue,fun he => (hD0 he).elim⟩
  let C (D : Finset X) : Finset X :=
    if hD : D ∈ B then Classical.choose (hlocal D hD) else ∅
  have hC (D : Finset X) (hD : D ∈ B) : C D ⊆ D ∧ b ∉ C D ∧
      (a ∈ D → a ∈ C D) ∧ (∃ x ∈ D, x ∉ C D) ∧
      (∃ y ∈ D, y ∈ C D) ∧ (D = b0 → C D = D \ {l,b}) := by
    simpa only [C,dif_pos hD] using Classical.choose_spec (hlocal D hD)
  let L := B.biUnion C
  have hLC {D : Finset X} (hD : D ∈ B) {x : X} (hxD : x ∈ D) :
      x ∈ L ↔ x ∈ C D := by
    constructor
    · intro hx
      obtain ⟨E,hE,hxC⟩ := mem_biUnion.mp hx
      by_cases hED : E = D
      · exact hED ▸ hxC
      · exact (Finset.disjoint_left.mp (h.right_rows_disjoint hE hD hED)
          ((hC E hE).1 hxC) hxD).elim
    · intro hx
      exact mem_biUnion.mpr ⟨D,hD,hx⟩
  obtain ⟨K,hKP,hK,hKJ,hmixK⟩ := h.exterior_colouring hn hinc
  let Blue := L ∪ K
  have hBlue : Blue ⊆ Ω.erase q := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨D,hD,hxC⟩ := mem_biUnion.mp hx
      have hxD := (hC D hD).1 hxC
      have hxΩ := (mem_minimalFamily.mp (h.right_minimal hD)).1 hxD
      have hxq : x ≠ q := by rintro rfl; exact h.no_q_right (fun ht => ht) hD hxD
      exact mem_erase.mpr ⟨hxq,hxΩ⟩
    · exact hK hx
  have hrestrict {D : Finset X} (hD : D ∈ B) {x : X} (hxD : x ∈ D) :
      x ∈ Blue ↔ x ∈ C D := by
    have hxK : x ∉ K := fun hx =>
      Finset.disjoint_left.mp (hKJ D (mem_union_right _ hD)) hx hxD
    constructor
    · intro hx
      exact (hLC hD hxD).mp ((mem_union.mp hx).resolve_right hxK)
    · intro hx
      exact mem_union_left _ ((hLC hD hxD).mpr hx)
  have hCb0 : C b0 = b0 \ {l,b} := (hC b0 hb0).2.2.2.2.2 rfl
  have hlnot : l ∉ Blue := by
    rw [hrestrict hb0 hl'.1,hCb0]
    simp
  have hrhoB : rho ∈ Blue := by
    rw [hrestrict hb0 hrho'.1,hCb0]
    exact mem_sdiff.mpr ⟨hrho'.1,by simp [hlrho.symm,hrhob]⟩
  have hportB {t : Finset X} (ht : t ∈ neighborhood M Ω q)
      {x : X} (hxt : x ∈ t) (hxq : x ≠ q) : ∃ D ∈ B, x ∈ D := by
    obtain ⟨s,hs,D,hD,hN⟩ := h.port t (mem_union_left _ ht) x hxt hxq
    refine ⟨D,hD,?_⟩
    exact (mem_neighborhood.mp (hN.symm ▸
      (by simp : D ∈ ({s,D} : Finset (Finset X))))).2
  obtain ⟨Da,hDa,haDa⟩ := hportB hu ha'.2 ha'.1
  have haB : a ∈ Blue := (hrestrict hDa haDa).mpr ((hC Da hDa).2.2.1 haDa)
  have hbnot : b ∉ Blue := by
    obtain ⟨Db,hDb,hbDb⟩ := hportB hv hb'.2 hb'.1
    exact fun hx => (hC Db hDb).2.1 ((hrestrict hDb hbDb).mp hx)
  have hlΩ := (mem_minimalFamily.mp (h.right_minimal hb0)).1 hl'.1
  have hbΩ := (mem_minimalFamily.mp (mem_neighborhood.mp hv).1).1 hb'.2
  have hlR : l ∈ Ω \ insert q Blue := by simp [hlΩ,hlq,hlnot]
  have hbR : b ∈ Ω \ insert q Blue := by simp [hbΩ,hb'.1,hbnot]
  refine ⟨Blue,hBlue,hlR,hrhoB,haB,hbR,?_,?_⟩
  · intro t ht
    by_cases htu : t = u
    · exact ⟨a,htu.symm ▸ ha'.2,haB⟩
    by_cases htv : t = v
    · exact ⟨rho,htv.symm ▸ hrho'.2,hrhoB⟩
    obtain ⟨x,hx⟩ := (mem_terminalNeighbors.mp (huni t ht)).2
    have hx' := mem_inter.mp hx
    have hxq : x ≠ q := by rintro rfl; exact h.no_q_right (fun ht => ht) hb0 hx'.1
    have hxl : x ≠ l := by
      intro he
      exact h.no_same_left ht hu
        ⟨(mem_neighborhood.mp ht).1,(mem_neighborhood.mp hu).1,htu,
          x,hxq,hx'.2,he.symm ▸ hl'.2⟩
    have hxb : x ≠ b := by
      intro he
      exact h.no_same_left ht hv
        ⟨(mem_neighborhood.mp ht).1,(mem_neighborhood.mp hv).1,htv,
          x,hxq,hx'.2,he.symm ▸ hb'.2⟩
    refine ⟨x,hx'.2,(hrestrict hb0 hx'.1).mpr ?_⟩
    rw [hCb0]
    exact mem_sdiff.mpr ⟨hx'.1,by simp [hxl,hxb]⟩
  · intro S hS hqS
    by_cases hSB : S ∈ B
    · obtain ⟨r,hrS,hrC⟩ := (hC S hSB).2.2.2.1
      obtain ⟨y,hyS,hyC⟩ := (hC S hSB).2.2.2.2.1
      have hrnot : r ∉ Blue := fun hx => hrC ((hrestrict hSB hrS).mp hx)
      have hrΩ := (mem_minimalFamily.mp hS).1 hrS
      have hrq : r ≠ q := by rintro rfl; exact hqS hrS
      exact ⟨⟨r,hrS,by simp [hrΩ,hrq,hrnot]⟩,
        y,hyS,(hrestrict hSB hyS).mpr hyC⟩
    · have hSP : S ∈ exteriorFamily M Ω q B := by
        apply mem_sdiff.mpr
        refine ⟨hS,?_⟩
        intro he
        rcases mem_union.mp he with hT | hB
        · exact hqS (mem_neighborhood.mp hT).2
        · exact hSB hB
      obtain ⟨⟨r,hrS,hrK⟩,y,hyS,hyK⟩ := hmixK S hSP
      have hrL : r ∉ L := by
        intro hx
        obtain ⟨D,hD,hrC⟩ := mem_biUnion.mp hx
        exact Finset.disjoint_left.mp
          (h.exterior_disjoint hSP (mem_union_right _ hD)) hrS ((hC D hD).1 hrC)
      have hrnot : r ∉ Blue := by simp [Blue,hrL,hrK]
      have hrΩ := (mem_minimalFamily.mp hS).1 hrS
      have hrq : r ≠ q := by rintro rfl; exact hqS hrS
      exact ⟨⟨r,hrS,by simp [hrΩ,hrq,hrnot]⟩,y,hyS,mem_union_right _ hyK⟩

/-- The actual universal neighbour branch, with its frame, every original
colour, every Complete decomposition and the literal word supplied here. -/
theorem original_universal_word {B : Finset (Finset X)}
    (h : RawBlock M Ω q (neighborhood M Ω q) B)
    (hqΩ : q ∈ Ω) (hr : 2 ≤ (neighborhood M Ω q).card)
    (hn : NoPrimitive M Ω)
    (hinc : ∀ x, x ≠ q → (neighborhood M Ω x).card ≤ 2)
    {b0 : Finset X} (hb0 : b0 ∈ B)
    (huni : ∀ t ∈ neighborhood M Ω q, t ∈ terminalNeighbors M Ω q b0) :
    ∃ w : List X, w.Perm Ω.toList ∧
      ∀ f : List X, f <:+: w → ¬Complete M Ω f.toFinset := by
  obtain ⟨u,hu,v,hv,huv,l,rho,a,b,hl,hrho,ha,hb,hal,hbrho,hnd⟩ :=
    universal_original_frame h hr hn hb0 huni
  obtain ⟨Blue,hBlue,hlR,hrhoB,haB,hbR,hterm,hmixed⟩ :=
    universal_mixed_colouring h hn hinc hb0 hu hv huni hl hrho ha hb hnd
  have port_pair {t : Finset X} (ht : t ∈ neighborhood M Ω q)
      {x : X} (hx0 : x ∈ b0) (hxt : x ∈ t) :
      neighborhood M Ω x = {t,b0} := by
    obtain ⟨s,hs,hxs,hN⟩ := h.right_port rfl hb0 hx0
    have htN : t ∈ ({s,b0} : Finset (Finset X)) := by
      rw [← hN]
      exact mem_neighborhood.mpr ⟨(mem_neighborhood.mp ht).1,hxt⟩
    have hts : t = s := by
      rcases mem_insert.mp htN with he | he
      · exact he
      · exact ((h.left_ne_right ht hb0) (mem_singleton.mp he)).elim
    simpa [hts] using hN
  refine ⟨universalWord Ω Blue q l rho,?_⟩
  apply universal_avoiding_word hqΩ hBlue hlR hrhoB hu hv huv
    (h.no_q_right (fun ht => ht) hb0) huni
    (port_pair hu (mem_inter.mp hl).1 (mem_inter.mp hl).2)
    (port_pair hv (mem_inter.mp hrho).1 (mem_inter.mp hrho).2)
    (mem_of_mem_erase hb) hbR hterm hmixed
  intro A hA
  obtain ⟨Q,hQP,hQI,hcover,hsum⟩ := complete_disjoint_decomposition hA
  exact ⟨Q,hQP,hQI,hcover⟩

/- The exact existing target definition is unchanged. Its proof follows. -/
def OriginalPositiveChargeTarget (H : Finset (Finset X)) (Ω : Finset X) (q : X) : Prop :=
  q ∈ Ω →
  2 ≤ (neighborhood (originalSpan H) Ω q).card →
  (∀ x, x ≠ q → (neighborhood (originalSpan H) Ω x).card ≤ 2) →
  ordinaryChargeGCD (originalSpan H) Ω q = (neighborhood (originalSpan H) Ω q).card →
    (∃ i ∈ Ω, ∃ c : Finset X → ℤ,
      (Pi.single i (1 : ℤ) : X → ℤ) = ∑ h ∈ H, c h • row h) ∨
    (∃ i ∈ Ω, ∃ j ∈ Ω, i ≠ j ∧ ∃ c : Finset X → ℤ,
      (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ) : X → ℤ) = ∑ h ∈ H, c h • row h) ∨
    ∃ w : List X, w.Perm Ω.toList ∧
      ∀ t : List X, t <:+: w → ¬Complete (originalSpan H) Ω t.toFinset

/-- EXACT OriginalPositiveChargeTarget: original finite-H integer ledgers
have leading coefficient ONE. Only the actual d=r positive branch is asserted; the zero-charge and
full ordering conclusions are separate obligations. -/
theorem original_positive_charge_target (H : Finset (Finset X))
    (Ω : Finset X) (q : X) : OriginalPositiveChargeTarget H Ω q := by
  intro hqΩ hr hinc hd
  by_cases hunit : ∃ i ∈ Ω, (Pi.single i (1 : ℤ) : X → ℤ) ∈ originalSpan H
  · obtain ⟨i,hi,hmem⟩ := hunit
    obtain ⟨c,hc⟩ := original_ledger hmem
    exact Or.inl ⟨i,hi,c,hc⟩
  by_cases hdiff : ∃ i ∈ Ω, ∃ j ∈ Ω, i ≠ j ∧
      (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ) : X → ℤ) ∈ originalSpan H
  · obtain ⟨i,hi,j,hj,hij,hmem⟩ := hdiff
    obtain ⟨c,hc⟩ := original_ledger hmem
    exact Or.inr (Or.inl ⟨i,hi,j,hj,hij,c,hc⟩)
  · have hn : NoPrimitive (originalSpan H) Ω := by
      constructor
      · intro i hi hmem
        exact hunit ⟨i,hi,hmem⟩
      · intro i hi j hj hij hmem
        exact hdiff ⟨i,hi,j,hj,hij,hmem⟩
    apply Or.inr
    apply Or.inr
    rcases original_positive_universal_or_word H hqΩ hr hinc hd hn with huni | hw
    · obtain ⟨B,hraw,b0,hb0,huniversal⟩ := huni
      exact original_universal_word hraw hqΩ hr hn hinc hb0 huniversal
    · exact hw

end PositiveChargeGeometry
end D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
