/- GID: D5/S3/Combinatorics/Sequenceability/PositiveChargeIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PositiveChargeIncidence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer potentials and ordinary charge force exact original terminal geometry. -/

import D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
import D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
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
  have he : (∑ x ∈ S, quotientLabel M x) =
      M.mkQ (∑ x ∈ S, Pi.single x (1 : ℤ)) :=
    (map_sum M.mkQ (fun x => Pi.single x (1 : ℤ)) S).symm
  rw [he]
  exact Submodule.Quotient.mk_eq_zero M

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
  have hcover' : A = Q.biUnion id := by
    ext x
    simpa only [Finset.mem_biUnion] using Finset.ext_iff.mp hcover x
  have hQA {S : Finset X} (hS : S ∈ Q) : S ⊆ A := by
    intro x hx
    rw [hcover']
    exact mem_biUnion.mpr ⟨S, hS, hx⟩
  refine ⟨Q, ?_, ?_, hcover', ?_⟩
  · intro S hS
    apply mem_minimalFamily.mpr
    refine ⟨(hQ S hS).1, (quotient_minimal_iff (hQ S hS).1 ?_).mp (hQ S hS).2⟩
    intro he
    exact hA.2.2.1 (hA.1.antisymm (he ▸ hQA hS))
  · intro S hS D hD hSD
    exact hdis hS hD hSD
  · simp_rw [row_eq_sum_single]
    rw [hcover']
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
    have hh' : h ∈ H := hh
    simp [hh']
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

theorem RawBlock.left_ne_right {A B : Finset (Finset X)}
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

theorem RawBlock.no_same_left {A B : Finset (Finset X)}
    (h : RawBlock M Ω q A B) {s t : Finset X} (hs : s ∈ A) (ht : t ∈ A) :
    ¬ OrdinaryAdj M Ω q s t := by
  intro hadj
  rcases (h.step (mem_union_left _ hs) hadj).2.1 with hab | hba
  · exact Finset.disjoint_left.mp h.disjoint ht hab.2
  · exact Finset.disjoint_left.mp h.disjoint hs hba.1

theorem RawBlock.no_q_right {A B : Finset (Finset X)}
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

theorem RawBlock.right_port {A B : Finset (Finset X)}
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
    exact hraw.no_q_right Subset.rfl hb
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

end PositiveChargeGeometry
end D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
