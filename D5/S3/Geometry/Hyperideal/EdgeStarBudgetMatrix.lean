/- GID: D5/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/EdgeStarBudgetMatrix
   mirror-E: none(waiver:finite-cyclic-face-incidence)
   anchors: []
   utility: none
   digest: Actual edge-star angle budgets as weighted face-signature transitions. -/

import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.EdgeStarBudgetMatrix

open D5.S3.Geometry.Hyperideal.FaceSignatureBalance
open D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions

/-- Opposite edges in the local order (12,13,14,34,24,23). -/
def opposite : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

/-- The four neighbouring occurrences are counted by position. -/
def highNeighbourCount (low : Fin 6 → Bool) (j : Fin 6) : ℕ :=
  ∑ k : Fin 6,
    if k = j ∨ k = opposite j then 0 else if low k then 0 else 1

/-- The three low-edge angle budgets indexed by high neighbours. -/
def beta : Nat → ℝ
  | 4 => Real.arccos (17 / 33)
  | 3 => Real.arccos (49 * Real.sqrt 6 / 198)
  | _ => Real.arccos (70 / 99)

/-- The five high-edge angle budgets from the high-face envelope. -/
def theta : Nat → ℝ
  | 0 => Real.arccos (31 / 33)
  | 1 => Real.arccos (25 / Real.sqrt 726)
  | 2 => Real.arccos (81 / 88)
  | 3 => Real.arccos (61 / Real.sqrt 4752)
  | _ => Real.arccos (23 / 27)

/-- False is face count one and true is face count two. -/
def lowMatrix (a b : Bool) : ℝ :=
  if a then (if b then beta 2 else beta 3)
  else if b then beta 3 else beta 4

def highMatrix (a b : Bool) : ℝ :=
  if a then (if b then theta 0 else theta 1)
  else if b then theta 1 else theta 2

/-- The actual number of directed face-signature transitions on one global edge. -/
noncomputable def transitionCount {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) (a b : Bool) : ℕ := by
  classical
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  exact ∑ i : s.Fiber e,
    if s.signature i.1 = a ∧ s.signature (s.next i.1) = b then 1 else 0

noncomputable def lowBudget {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℝ := by
  classical
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  exact ∑ i : s.Fiber e, beta (highNeighbourCount (s.localColor i.1) i.1.2)

noncomputable def highBudget {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℝ := by
  classical
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  exact ∑ i : s.Fiber e, theta (highNeighbourCount (s.localColor i.1) i.1.2)

noncomputable def lowMatrixTotal {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, (transitionCount s e a b : ℝ) * lowMatrix a b

noncomputable def highMatrixTotal {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, (transitionCount s e a b : ℝ) * highMatrix a b

/-- Every paired face slot lies in one oriented edge cycle, whichever of its
two incident faces is outgoing. -/
private theorem edge_step_same_cycle {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge)
    (hpair : ∀ x, s.facePair (s.facePair x) = x)
    (hmap : ∀ x n, s.faceMap (s.facePair x) (s.faceMap x n) = n)
    (i j : Occurrence T)
    (hstep : ∃ (x : T × Fin 4) (n : Fin 3),
      i = (x.1, faceEdge x.2 n) ∧
      j = ((s.facePair x).1,
        faceEdge (s.facePair x).2 (s.faceMap x n))) :
    s.next.SameCycle i j := by
  let incomingSlot (r : Occurrence T → Bool) (z : Occurrence T) : Fin 3 :=
    if r z then (edgeFaceSlots z.2).2 else (edgeFaceSlots z.2).1
  have slot_cases (x : T × Fin 4) (n : Fin 3) :
      let z : Occurrence T := (x.1, faceEdge x.2 n)
      (x.2 = outgoingFace s.reversed z ∧ n = outgoingSlot s.reversed z) ∨
        (x.2 = incomingFace s.reversed z ∧ n = incomingSlot s.reversed z) := by
    dsimp
    rcases x with ⟨t, f⟩
    cases hr : s.reversed (t, faceEdge f n) <;>
      fin_cases f <;> fin_cases n <;>
      simp [outgoingFace, incomingFace, outgoingSlot, incomingSlot,
        edgeFaces, edgeFaceSlots, faceEdge]
  have hslotTable (v : Fin 6) (b : Bool) :
      faceEdge (if b then (edgeFaces v).1 else (edgeFaces v).2)
        (if b then (edgeFaceSlots v).1 else (edgeFaceSlots v).2) = v := by
    cases b <;> fin_cases v <;> decide
  have hslot (z : Occurrence T) :
      faceEdge (outgoingFace s.reversed z) (outgoingSlot s.reversed z) = z.2 := by
    simpa [outgoingFace, outgoingSlot] using hslotTable z.2 (s.reversed z)
  have hfaceInj (f : Fin 4) : Function.Injective (faceEdge f) := by
    fin_cases f <;> decide
  rcases hstep with ⟨x, n, rfl, rfl⟩
  let i : Occurrence T := (x.1, faceEdge x.2 n)
  let j : Occurrence T :=
    ((s.facePair x).1, faceEdge (s.facePair x).2 (s.faceMap x n))
  change s.next.SameCycle i j
  rcases slot_cases x n with hout | hin
  · have hnext : s.next i = j := by
      change rawNext s.facePair s.faceMap s.reversed i = j
      simp only [rawNext, i, j]
      rw [← hout.1, ← hout.2]
    rw [← hnext]
    exact (Equiv.Perm.sameCycle_apply_right).mpr (Equiv.Perm.SameCycle.refl s.next i)
  · let k : Occurrence T := s.next.symm i
    have hki : s.next k = i := s.next.apply_symm_apply i
    let source : T × Fin 4 := (k.1, outgoingFace s.reversed k)
    have hpaired : s.facePair source = (i.1, incomingFace s.reversed i) := by
      apply Prod.ext
      · have h := congrArg Prod.fst hki
        change (s.facePair source).1 = i.1 at h
        exact h
      · have h := s.entersFace k
        change incomingFace s.reversed (s.next k) =
          (s.facePair (k.1, outgoingFace s.reversed k)).2 at h
        rw [hki] at h
        exact h.symm
    have hx : x = s.facePair source := by
      apply Prod.ext
      · exact (congrArg Prod.fst hpaired).symm
      · exact hin.1.trans (congrArg Prod.snd hpaired).symm
    have hedge :
        faceEdge (s.facePair source).2
          (s.faceMap source (outgoingSlot s.reversed k)) = i.2 := by
      have h := congrArg Prod.snd hki
      change faceEdge (s.facePair source).2
        (s.faceMap source (outgoingSlot s.reversed k)) = i.2 at h
      exact h
    have hn : s.faceMap source (outgoingSlot s.reversed k) = n := by
      apply hfaceInj x.2
      calc
        faceEdge x.2 (s.faceMap source (outgoingSlot s.reversed k)) =
            faceEdge (s.facePair source).2
              (s.faceMap source (outgoingSlot s.reversed k)) := by rw [hx]
        _ = i.2 := hedge
        _ = faceEdge x.2 n := rfl
    have hback : s.faceMap x n = outgoingSlot s.reversed k := by
      rw [hx, ← hn]
      exact hmap source (outgoingSlot s.reversed k)
    have hjk : j = k := by
      apply Prod.ext
      · change (s.facePair x).1 = k.1
        rw [hx, hpair]
      · change faceEdge (s.facePair x).2 (s.faceMap x n) = k.2
        rw [hback, hx, hpair]
        exact hslot k
    rw [hjk]
    have hcycle : s.next.SameCycle k i := by
      rw [← hki]
      exact (Equiv.Perm.sameCycle_apply_right).mpr
        (Equiv.Perm.SameCycle.refl s.next k)
    exact hcycle.symm

/-- Actual edge classes are exactly the successor cycles of the raw pairing;
each local occurrence contributes its angle budget once. -/
theorem actual_edge_budget_matrix {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color) (e : p.GlobalEdge) :
    let s := (p.toFacePairedTriangulation color valid).edgeStars
    (∀ i j : Occurrence T,
      s.next.SameCycle i j ↔ s.globalEdge i = s.globalEdge j) ∧
    (∀ i : Occurrence T, s.globalEdge (s.next i) = s.globalEdge i) ∧
    (s.color e = true →
      lowBudget s e = lowMatrixTotal s e ∧
        (lowBudget s e > 2 * Real.pi ↔ lowMatrixTotal s e > 2 * Real.pi)) ∧
    (s.color e = false →
      highBudget s e = highMatrixTotal s e ∧
        (highBudget s e > 2 * Real.pi ↔ highMatrixTotal s e > 2 * Real.pi)) := by
  let s := (p.toFacePairedTriangulation color valid).edgeStars
  have hg :
      (∀ i : Occurrence T, s.globalEdge (s.next i) = s.globalEdge i) ∧
      (s.color e = true →
        lowBudget s e = lowMatrixTotal s e ∧
          (lowBudget s e > 2 * Real.pi ↔ lowMatrixTotal s e > 2 * Real.pi)) ∧
      (s.color e = false →
        highBudget s e = highMatrixTotal s e ∧
          (highBudget s e > 2 * Real.pi ↔ highMatrixTotal s e > 2 * Real.pi)) := by
    classical
    letI : Fintype (s.Fiber e) := Subtype.fintype _
    have hslotTable (j : Fin 6) (b : Bool) :
        faceEdge (if b then (edgeFaces j).1 else (edgeFaces j).2)
          (if b then (edgeFaceSlots j).1 else (edgeFaceSlots j).2) = j := by
      cases b <;> fin_cases j <;> decide
    have hslot (i : Occurrence T) :
        faceEdge (s.outgoing i) (outgoingSlot s.reversed i) = i.2 := by
      simpa [EdgeStars.outgoing, outgoingFace, outgoingSlot] using
        hslotTable i.2 (s.reversed i)
    have hpres (i : Occurrence T) :
        s.globalEdge (s.next i) = s.globalEdge i := by
      let x : T × Fin 4 := (i.1, s.outgoing i)
      let n := outgoingSlot s.reversed i
      have hf := s.faceLabels x n
      calc
        s.globalEdge (s.next i) =
            s.edgeLabel (s.facePair x).1
              (faceEdge (s.facePair x).2 (s.faceMap x n)) := by
          change s.globalEdge (rawNext s.facePair s.faceMap s.reversed i) = _
          rfl
        _ = s.edgeLabel x.1 (faceEdge x.2 n) := hf.symm
        _ = s.globalEdge i := by simp [x, n, EdgeStars.globalEdge, hslot i]
    have hnext (i : Occurrence T) :
        s.signature (s.next i) =
          decide (faceLowCount (s.localColor i) (s.outgoing i) = 2) :=
      (path_end_signature_and_next s i).2
    have hlowComm (a b : Bool) : lowMatrix a b = lowMatrix b a := by
      cases a <;> cases b <;> rfl
    have hhighComm (a b : Bool) : highMatrix a b = highMatrix b a := by
      cases a <;> cases b <;> rfl
    have hweight (i : s.Fiber e) :
        (if s.color e then beta (highNeighbourCount (s.localColor i.1) i.1.2)
          else theta (highNeighbourCount (s.localColor i.1) i.1.2)) =
        (if s.color e then lowMatrix (s.signature i.1) (s.signature (s.next i.1))
          else highMatrix (s.signature i.1) (s.signature (s.next i.1))) := by
      have hcolor : s.localColor i.1 i.1.2 = s.color e := by
        change s.color (s.globalEdge i.1) = s.color e
        rw [i.2]
      let low := s.localColor i.1
      let j := i.1.2
      have hlocal :
          (if low j then beta (highNeighbourCount low j)
            else theta (highNeighbourCount low j)) =
          (if low j then
            lowMatrix (decide (faceLowCount low (edgeFaces j).1 = 2))
              (decide (faceLowCount low (edgeFaces j).2 = 2))
          else
            highMatrix (decide (faceLowCount low (edgeFaces j).1 = 2))
              (decide (faceLowCount low (edgeFaces j).2 = 2))) := by
        have ha : faceLowCount low (edgeFaces j).1 = 1 ∨
            faceLowCount low (edgeFaces j).1 = 2 :=
          (s.valid i.1) (edgeFaces j).1
        have hb : faceLowCount low (edgeFaces j).2 = 1 ∨
            faceLowCount low (edgeFaces j).2 = 2 :=
          (s.valid i.1) (edgeFaces j).2
        have hc : highNeighbourCount low j +
            faceLowCount low (edgeFaces j).1 + faceLowCount low (edgeFaces j).2 =
            if low j then 6 else 4 := by
          have hbits : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ j : Fin 6,
              highNeighbourCount ![b0, b1, b2, b3, b4, b5] j +
                faceLowCount ![b0, b1, b2, b3, b4, b5] (edgeFaces j).1 +
                faceLowCount ![b0, b1, b2, b3, b4, b5] (edgeFaces j).2 =
                if (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) j then 6 else 4 := by
            intro b0 b1 b2 b3 b4 b5 j
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
              cases b4 <;> cases b5 <;> fin_cases j <;>
              decide
          have hvec : ![low 0, low 1, low 2, low 3, low 4, low 5] = low := by
            funext i
            fin_cases i <;> rfl
          rw [← hvec]
          exact hbits (low 0) (low 1) (low 2) (low 3) (low 4) (low 5) j
        have hk : highNeighbourCount low j =
            (if low j then 6 else 4) -
              (faceLowCount low (edgeFaces j).1 +
                faceLowCount low (edgeFaces j).2) := by
          omega
        rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          cases hj : low j <;>
          simp [hk, ha, hb, hj, beta, theta, lowMatrix, highMatrix]
      have horient :
          (if s.localColor i.1 i.1.2 then beta (highNeighbourCount (s.localColor i.1) i.1.2)
            else theta (highNeighbourCount (s.localColor i.1) i.1.2)) =
          (if s.localColor i.1 i.1.2 then
            lowMatrix (decide (faceLowCount (s.localColor i.1) (s.incoming i.1) = 2))
              (decide (faceLowCount (s.localColor i.1) (s.outgoing i.1) = 2))
           else
            highMatrix (decide (faceLowCount (s.localColor i.1) (s.incoming i.1) = 2))
              (decide (faceLowCount (s.localColor i.1) (s.outgoing i.1) = 2))) := by
        cases hr : s.reversed i.1
        · simpa [low, j, EdgeStars.incoming, EdgeStars.outgoing, incomingFace,
            outgoingFace, hr]
            using hlocal
        · simpa [low, j, EdgeStars.incoming, EdgeStars.outgoing, incomingFace,
            outgoingFace, hr, hlowComm, hhighComm] using hlocal
      rw [hcolor] at horient
      rw [← hnext i.1] at horient
      exact horient
    have hgroup (W : Bool → Bool → ℝ) :
        (∑ a : Bool, ∑ b : Bool, (transitionCount s e a b : ℝ) * W a b) =
          ∑ i : s.Fiber e, W (s.signature i.1) (s.signature (s.next i.1)) := by
      have hpoint (i : s.Fiber e) :
          (∑ a : Bool, ∑ b : Bool,
            (if s.signature i.1 = a ∧ s.signature (s.next i.1) = b
              then (1 : ℝ) else 0) * W a b) =
            W (s.signature i.1) (s.signature (s.next i.1)) := by
        cases ha : s.signature i.1 <;> cases hb : s.signature (s.next i.1) <;>
          simp [Fintype.sum_bool, ha, hb]
      simp only [transitionCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, Finset.sum_mul]
      calc
        (∑ a : Bool, ∑ b : Bool, ∑ i : s.Fiber e,
            (if s.signature i.1 = a ∧ s.signature (s.next i.1) = b
              then (1 : ℝ) else 0) * W a b) =
            ∑ a : Bool, ∑ i : s.Fiber e, ∑ b : Bool,
              (if s.signature i.1 = a ∧ s.signature (s.next i.1) = b
                then (1 : ℝ) else 0) * W a b := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = ∑ i : s.Fiber e, ∑ a : Bool, ∑ b : Bool,
              (if s.signature i.1 = a ∧ s.signature (s.next i.1) = b
                then (1 : ℝ) else 0) * W a b := by
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_congr rfl (fun i _ => hpoint i)
    refine ⟨hpres, ?_, ?_⟩
    · intro he
      have heq : lowBudget s e = lowMatrixTotal s e := by
        unfold lowBudget lowMatrixTotal
        rw [hgroup lowMatrix]
        apply Finset.sum_congr rfl
        intro i _
        simpa [he] using hweight i
      exact ⟨heq, by rw [heq]⟩
    · intro he
      have heq : highBudget s e = highMatrixTotal s e := by
        unfold highBudget highMatrixTotal
        rw [hgroup highMatrix]
        apply Finset.sum_congr rfl
        intro i _
        simpa [he] using hweight i
      exact ⟨heq, by rw [heq]⟩
  refine ⟨?_, hg⟩
  have hpair (x : T × Fin 4) : s.facePair (s.facePair x) = x := by
    change p.facePair (p.facePair x) = x
    have h := congrArg (fun f : Equiv.Perm (T × Fin 4) => f x) p.pairInvolutive
    simpa using h
  have hmap (x : T × Fin 4) (n : Fin 3) :
      s.faceMap (s.facePair x) (s.faceMap x n) = n := by
    change p.faceMap (p.facePair x) (p.faceMap x n) = n
    exact p.mapInverse x n
  have hrel (a b : Occurrence T) (h : p.edgeStep a b) :
      s.next.SameCycle a b := by
    apply edge_step_same_cycle s hpair hmap a b
    exact h
  have heqv (a b : Occurrence T) (h : Relation.EqvGen p.edgeStep a b) :
      s.next.SameCycle a b := by
    induction h with
    | rel a b h => exact hrel a b h
    | refl a => exact Equiv.Perm.SameCycle.refl s.next a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ hab hbc => exact hab.trans hbc
  have hpow (n : ℕ) : ∀ z : Occurrence T,
      s.globalEdge ((s.next ^ n) z) = s.globalEdge z := by
    induction n with
    | zero => intro z; simp
    | succ n ih =>
        intro z
        rw [pow_succ, Equiv.Perm.mul_apply, ih (s.next z), hg.1 z]
  intro i j
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn]
    exact (hpow n i).symm
  · intro h
    have hq : p.edgeLabel i.1 i.2 = p.edgeLabel j.1 j.2 := h
    exact heqv i j (Quotient.exact hq)

#print axioms actual_edge_budget_matrix

end D5.S3.Geometry.Hyperideal.EdgeStarBudgetMatrix
