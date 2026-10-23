/- GID: D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.claim; result=D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.result; claim=D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.claim
   digest: Actual K4 signed ribbons and finite event transports exclude exact thirds under the uniform independent fair-bit law. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FacialRandomEmbeddings.K4SignedRotation

namespace FiniteEvents

open scoped BigOperators

variable {Ω E : Type*} [Fintype Ω] [Fintype E]
variable (T : Ω → E → Prop) [DecidableRel T]

/-- The number of equally weighted states in which an indexed event occurs. -/
def eventCount (e : E) : ℕ := ∑ ω : Ω, if T ω e then 1 else 0

/-- Count incidences first over states, then over event indices. -/
def totalCount : ℕ := ∑ ω : Ω, ∑ e : E, if T ω e then 1 else 0

/-- The exact mean number of events under the uniform law on the state space. -/
def uniformExpectedCount : ℚ := (totalCount T : ℚ) / Fintype.card Ω

omit [Fintype E] in
/-- An event-preserving state bijection equates two marginal counts.
This proves the marginal equality from the transport instead of assuming it. -/
theorem event_count_eq_of_equiv (e f : E) (φ : Ω ≃ Ω)
    (hφ : ∀ ω, T (φ ω) f ↔ T ω e) :
    eventCount T e = eventCount T f := by
  apply Fintype.sum_equiv φ
  intro ω
  simp only [hφ ω]

/-- If every event is transported from one root event, the two orders of
counting incidences give the number of events times the root marginal count. -/
theorem total_count_eq_card_mul (root : E)
    (transport : ∀ e : E, ∃ φ : Ω ≃ Ω, ∀ ω, T (φ ω) e ↔ T ω root) :
    totalCount T = Fintype.card E * eventCount T root := by
  unfold totalCount
  rw [Finset.sum_comm]
  calc
    (∑ e : E, ∑ ω : Ω, if T ω e then 1 else 0) =
        ∑ _e : E, eventCount T root := by
      apply Finset.sum_congr rfl
      intro e _
      obtain ⟨φ, hφ⟩ := transport e
      exact (event_count_eq_of_equiv T root e φ hφ).symm
    _ = Fintype.card E * eventCount T root := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/-- In a nonempty uniform finite model with event transports, a mean of
the number of events divided by q forces q to divide the number of states. -/
theorem expected_denominator_dvd [Nonempty Ω] (root : E)
    (transport : ∀ e : E, ∃ φ : Ω ≃ Ω, ∀ ω, T (φ ω) e ↔ T ω root)
    (q : ℕ) (hq : q ≠ 0)
    (hmean : uniformExpectedCount T = (Fintype.card E : ℚ) / q) :
    q ∣ Fintype.card Ω := by
  have hΩ : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let : Nonempty E := ⟨root⟩
  have hE : (Fintype.card E : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  unfold uniformExpectedCount at hmean
  rw [total_count_eq_card_mul T root transport, Nat.cast_mul] at hmean
  have hm := (div_eq_div_iff hΩ hqQ).mp hmean
  have hk : (q : ℚ) * eventCount T root = Fintype.card Ω := by
    apply (mul_left_cancel₀ hE)
    calc
      (Fintype.card E : ℚ) * ((q : ℚ) * eventCount T root) =
          ((Fintype.card E : ℚ) * eventCount T root) * q := by ring
      _ = (Fintype.card E : ℚ) * Fintype.card Ω := hm
  have hkN : q * eventCount T root = Fintype.card Ω := by exact_mod_cast hk
  exact ⟨eventCount T root, hkN.symm⟩

/-- A dyadic uniform sample space cannot have one third of a nonempty
transitive event family in expectation. No assumption about equal marginals
is needed: the transports imply it. -/
theorem dyadic_expected_count_ne_third (root : E)
    (transport : ∀ e : E, ∃ φ : Ω ≃ Ω, ∀ ω, T (φ ω) e ↔ T ω root)
    (r : ℕ) (hcard : Fintype.card Ω = 2 ^ r) :
    uniformExpectedCount T ≠ (Fintype.card E : ℚ) / 3 := by
  have hpos : 0 < Fintype.card Ω := by rw [hcard]; exact pow_pos (by decide) _
  let : Nonempty Ω := Fintype.card_pos_iff.mp hpos
  intro hmean
  have hdiv := expected_denominator_dvd T root transport 3 (by decide) hmean
  rw [hcard] at hdiv
  have htwo : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hdiv
  norm_num at htwo

end FiniteEvents

open scoped BigOperators

/-- Four independent rotation bits and six independent band-twist bits. -/
abbrev State := Fin 16 × Fin 64
abbrev Edge := Fin 6
abbrev Flag := Fin 24

/-- Edge order is 01, 02, 03, 12, 13, 23. Its four flags are
(lower endpoint, side 0/1), then (upper endpoint, side 0/1). -/
def vertex : Flag → Fin 4 :=
  ![0,0,1,1,0,0,2,2,0,0,3,3,1,1,2,2,1,1,3,3,2,2,3,3]

def bit (mask index : ℕ) : ℕ := mask / 2 ^ index % 2

/-- Adjacent corners of a vertex disk. Bit zero uses the ascending cyclic
neighbour order; bit one reverses it. The corner operation reverses side. -/
def corner (r : Fin 16) (x : Flag) : Flag :=
  if bit r.val (vertex x).val = 0 then
    ![9,4,17,12,1,8,21,14,5,0,23,18,3,16,7,20,13,2,11,22,15,6,19,10] x
  else
    ![5,8,13,16,9,0,15,20,1,4,19,22,17,2,21,6,3,12,23,10,7,14,11,18] x

/-- Across a band, untwisted bit zero reverses side and twisted bit one
preserves side. This is the complement of the author's lambda-bit convention. -/
def band (t : Fin 64) (x : Flag) : Flag :=
  ⟨(4 * (x.val / 4) + 2 * (1 - x.val / 2 % 2) +
      (x.val % 2 + 1 + bit t.val (x.val / 4)) % 2) % 24,
    Nat.mod_lt _ (by decide)⟩

private theorem corner_involutive : ∀ r : Fin 16, Function.Involutive (corner r) := by
  change ∀ (r : Fin 16) (x : Flag), corner r (corner r x) = x
  decide +kernel
private theorem band_involutive : ∀ t : Fin 64, Function.Involutive (band t) := by
  change ∀ (t : Fin 64) (x : Flag), band t (band t x) = x
  decide +kernel
private theorem corner_no_fixed : ∀ (r : Fin 16) (x : Flag), corner r x ≠ x := by
  decide +kernel
private theorem band_no_fixed : ∀ (t : Fin 64) (x : Flag), band t x ≠ x := by
  decide +kernel

/-- The two fixed-point-free matchings of the ribbon-boundary flag graph. -/
def cornerPerm (r : Fin 16) : Equiv.Perm Flag where
  toFun := corner r
  invFun := corner r
  left_inv := corner_involutive r
  right_inv := corner_involutive r

def bandPerm (t : Fin 64) : Equiv.Perm Flag where
  toFun := band t
  invFun := band t
  left_inv := band_involutive t
  right_inv := band_involutive t

/-- One step along an oriented physical boundary: band first, then corner. -/
def facePerm (s : State) : Equiv.Perm Flag := cornerPerm s.1 * bandPerm s.2

def edgeFlag (e : Edge) (j : Fin 4) : Flag :=
  ⟨(4 * e.val + j.val) % 24, Nat.mod_lt _ (by decide)⟩

/-- 0 = good singular (same directed traversal), 1 = bad singular
(opposite traversals), 2 = regular (two physical boundary components).
SameCycle is the genuine integer-power orbit relation. Its mathlib decision
procedure checks 24 iterates, with a proved finite-orbit bound. -/
def edgeType (s : State) (e : Edge) : Fin 3 :=
  if (facePerm s).SameCycle (edgeFlag e 0) (edgeFlag e 1) then 0
  else if (facePerm s).SameCycle (corner s.1 (edgeFlag e 0)) (edgeFlag e 1) then 1
  else 2

/-- Physical boundary connectivity is alternating corner/band connectivity. -/
def BoundaryConnected (s : State) (x y : Flag) : Prop :=
  PerfectMatchings.InvolutionOrbitSplit.Connected (cornerPerm s.1) (bandPerm s.2) x y

/-- The physical category, without a bounded-orbit or lookup-table assumption.
Good means the same oriented product orbit; bad means its opposite oriented
orbit in the same physical component; regular means distinct components.
Fixed-point-freeness makes the two oriented orbits disjoint. -/
def HasType (ty : Fin 3) (s : State) (e : Edge) : Prop :=
  let sameDirection := (facePerm s).SameCycle (edgeFlag e 0) (edgeFlag e 1)
  let sameBoundary := BoundaryConnected s (edgeFlag e 0) (edgeFlag e 1)
  if ty = 0 then sameDirection
  else if ty = 1 then
    (facePerm s).SameCycle (corner s.1 (edgeFlag e 0)) (edgeFlag e 1)
  else ¬sameBoundary

/-- The finite classifier is exactly the physical boundary classification. -/
theorem classification_iff (ty : Fin 3) (s : State) (e : Edge) :
    edgeType s e = ty ↔ HasType ty s e := by
  have hs := PerfectMatchings.InvolutionOrbitSplit.component_split
    (cornerPerm s.1) (bandPerm s.2) (corner_involutive s.1) (band_involutive s.2)
    (corner_no_fixed s.1) (band_no_fixed s.2) (edgeFlag e 0)
  have hdis : ¬ ((facePerm s).SameCycle (edgeFlag e 0) (edgeFlag e 1) ∧
      (facePerm s).SameCycle (corner s.1 (edgeFlag e 0)) (edgeFlag e 1)) := by
    rintro ⟨ha, hb⟩
    exact Set.disjoint_left.mp hs.1 ha hb
  have hc := PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits
    (cornerPerm s.1) (bandPerm s.2) (corner_involutive s.1) (band_involutive s.2)
    (edgeFlag e 0) (edgeFlag e 1)
  change BoundaryConnected s (edgeFlag e 0) (edgeFlag e 1) ↔
    (facePerm s).SameCycle (edgeFlag e 0) (edgeFlag e 1) ∨
    (facePerm s).SameCycle (corner s.1 (edgeFlag e 0)) (edgeFlag e 1) at hc
  fin_cases ty <;> simp only [HasType, hc, edgeType] <;> split_ifs <;> simp_all

instance hasTypeDecidable (ty : Fin 3) : DecidableRel (HasType ty) :=
  fun s e => decidable_of_iff (edgeType s e = ty) (classification_iff ty s e)

/-- Endpoint-preserving vertex relabellings taking 01 to each labelled edge.
The Boolean selects the inverse map when true. -/
def vertexRelabel (inverse : Bool) : Edge → Fin 4 → Fin 4 :=
  if inverse then
    ![![0,1,2,3],
      ![0,2,1,3],
      ![0,3,2,1],
      ![2,0,1,3],
      ![3,0,2,1],
      ![2,3,0,1]]
  else
    ![![0,1,2,3],
      ![0,2,1,3],
      ![0,3,2,1],
      ![1,2,0,3],
      ![1,3,2,0],
      ![2,3,0,1]]

def edgeRelabel (inverse : Bool) : Edge → Edge → Edge :=
  if inverse then
    ![![0,1,2,3,4,5],
      ![1,0,2,3,5,4],
      ![2,1,0,5,4,3],
      ![1,3,5,0,2,4],
      ![2,5,4,1,0,3],
      ![5,1,3,2,4,0]]
  else
    ![![0,1,2,3,4,5],
      ![1,0,2,3,5,4],
      ![2,1,0,5,4,3],
      ![3,0,4,1,5,2],
      ![4,3,0,5,2,1],
      ![5,1,3,2,4,0]]

private def permuteMask {n : ℕ} (p : Fin n → Fin n) (mask : ℕ) : ℕ :=
  ∑ i : Fin n, bit mask (p i).val * 2 ^ i.val

/-- Offsets record transport of the ascending local cyclic orders. -/
def rotationRelabel (inverse : Bool) (k : Edge) (r : Fin 16) : Fin 16 :=
  let offset : ℕ := if inverse then ![0,9,15,3,9,0] k else ![0,9,15,6,3,0] k
  ⟨(Nat.xor (permuteMask (vertexRelabel (!inverse) k) r.val) offset) % 16,
    Nat.mod_lt _ (by decide)⟩

def twistRelabel (inverse : Bool) (k : Edge) (t : Fin 64) : Fin 64 :=
  ⟨permuteMask (edgeRelabel (!inverse) k) t.val % 64, Nat.mod_lt _ (by decide)⟩

private theorem rotation_inverse_check : ∀ (k : Edge) (r : Fin 16),
    rotationRelabel true k (rotationRelabel false k r) = r ∧
    rotationRelabel false k (rotationRelabel true k r) = r := by
  decide +kernel
private theorem twist_inverse_check : ∀ (k : Edge) (t : Fin 64),
    twistRelabel true k (twistRelabel false k t) = t ∧
    twistRelabel false k (twistRelabel true k t) = t := by
  decide +kernel

/-- Every transport is a bijection of the full 1024-outcome fair-bit space. -/
def stateRelabel (k : Edge) : State ≃ State where
  toFun s := (rotationRelabel false k s.1, twistRelabel false k s.2)
  invFun s := (rotationRelabel true k s.1, twistRelabel true k s.2)
  left_inv s := Prod.ext (rotation_inverse_check k s.1).1 (twist_inverse_check k s.2).1
  right_inv s := Prod.ext (rotation_inverse_check k s.1).2 (twist_inverse_check k s.2).2

/-- The flag maps preserve side and apply the actual vertex permutation. -/
def flagMap (inverse : Bool) : Edge → Flag → Flag :=
  if inverse then
    ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],
      ![4,5,6,7,0,1,2,3,8,9,10,11,14,15,12,13,20,21,22,23,16,17,18,19],
      ![8,9,10,11,4,5,6,7,0,1,2,3,22,23,20,21,18,19,16,17,14,15,12,13],
      ![6,7,4,5,14,15,12,13,20,21,22,23,0,1,2,3,8,9,10,11,16,17,18,19],
      ![10,11,8,9,22,23,20,21,18,19,16,17,4,5,6,7,0,1,2,3,14,15,12,13],
      ![20,21,22,23,6,7,4,5,14,15,12,13,10,11,8,9,18,19,16,17,0,1,2,3]]
  else
    ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],
      ![4,5,6,7,0,1,2,3,8,9,10,11,14,15,12,13,20,21,22,23,16,17,18,19],
      ![8,9,10,11,4,5,6,7,0,1,2,3,22,23,20,21,18,19,16,17,14,15,12,13],
      ![12,13,14,15,2,3,0,1,16,17,18,19,6,7,4,5,20,21,22,23,8,9,10,11],
      ![16,17,18,19,12,13,14,15,2,3,0,1,22,23,20,21,10,11,8,9,6,7,4,5],
      ![20,21,22,23,6,7,4,5,14,15,12,13,10,11,8,9,18,19,16,17,0,1,2,3]]

private theorem flag_inverse_check : ∀ (k : Edge) (x : Flag),
    flagMap true k (flagMap false k x) = x ∧
    flagMap false k (flagMap true k x) = x := by
  decide +kernel

def flagRelabel (k : Edge) : Equiv.Perm Flag where
  toFun := flagMap false k
  invFun := flagMap true k
  left_inv x := (flag_inverse_check k x).1
  right_inv x := (flag_inverse_check k x).2

/-- Relabelling intertwines the two corner matchings. -/
private theorem corner_transport : ∀ (k : Edge) (r : Fin 16) (x : Flag),
    flagRelabel k (corner r x) =
      corner (rotationRelabel false k r) (flagRelabel k x) := by
  intro k
  fin_cases k <;> decide +kernel

/-- Relabelling intertwines the two band matchings. -/
private theorem band_transport : ∀ (k : Edge) (t : Fin 64) (x : Flag),
    flagRelabel k (band t x) =
      band (twistRelabel false k t) (flagRelabel k x) := by
  intro k
  fin_cases k <;> decide +kernel

private theorem root_flags_transport : ∀ k : Edge,
    flagRelabel k (edgeFlag 0 0) = edgeFlag k 0 ∧
    flagRelabel k (edgeFlag 0 1) = edgeFlag k 1 := by
  decide +kernel

private theorem face_conjugacy (k : Edge) (s : State) :
    facePerm (stateRelabel k s) =
      flagRelabel k * facePerm s * (flagRelabel k)⁻¹ := by
  have hc (x : Flag) :
      facePerm (stateRelabel k s) (flagRelabel k x) = flagRelabel k (facePerm s x) := by
    change corner (rotationRelabel false k s.1)
      (band (twistRelabel false k s.2) (flagRelabel k x)) =
      flagRelabel k (corner s.1 (band s.2 x))
    rw [← band_transport, ← corner_transport]
  apply Equiv.ext
  intro x
  simpa only [Equiv.apply_symm_apply, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv] using
    hc ((flagRelabel k).symm x)

/-- The classifier is equivariant because actual flag relabelling conjugates
the corner and band matchings, hence the entire oriented-boundary permutation. -/
private theorem edge_type_transport (k : Edge) (s : State) :
    edgeType (stateRelabel k s) k = edgeType s 0 := by
  have horbit (x y : Flag) :
      (facePerm (stateRelabel k s)).SameCycle (flagRelabel k x) (flagRelabel k y) ↔
        (facePerm s).SameCycle x y := by
    rw [face_conjugacy, Equiv.Perm.sameCycle_conj]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  obtain ⟨ha, hb⟩ := root_flags_transport k
  unfold edgeType
  rw [← ha, ← hb]
  change (if (facePerm (stateRelabel k s)).SameCycle
      (flagRelabel k (edgeFlag 0 0)) (flagRelabel k (edgeFlag 0 1)) then (0 : Fin 3)
    else if (facePerm (stateRelabel k s)).SameCycle
      (corner (rotationRelabel false k s.1) (flagRelabel k (edgeFlag 0 0)))
      (flagRelabel k (edgeFlag 0 1)) then 1 else 2) = _
  simp only [← corner_transport, horbit]



/-- At least one physical edge type has expected count one third of six,
under the uniform law on all independently chosen rotations and twist bits. -/
def claim : Prop :=
  ∃ ty : Fin 3, FiniteEvents.uniformExpectedCount (HasType ty) =
    (Fintype.card Edge : ℚ) / 3

/-- All three exact-third equalities fail for the unconditioned independent
fair signed-rotation law. No claim is made for an unspecified or nonuniform
law on unlabelled embeddings, nor for a genus/orientability-conditioned law. -/
theorem result : ¬ claim := by
  rintro ⟨ty, ht⟩
  apply FiniteEvents.dyadic_expected_count_ne_third
    (HasType ty) (0 : Edge) ?_ 10 (by norm_num [State, Fintype.card_prod]) ht
  intro e
  refine ⟨stateRelabel e, ?_⟩
  intro s
  rw [← classification_iff ty (stateRelabel e s) e,
    ← classification_iff ty s 0, edge_type_transport e s]

#print axioms classification_iff
#print axioms result

end D5.S3.Combinatorics.FacialRandomEmbeddings.K4SignedRotation
