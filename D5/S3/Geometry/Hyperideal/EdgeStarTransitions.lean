/- GID: D5/S3/Geometry/Hyperideal/EdgeStarTransitions
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/EdgeStarTransitions
   mirror-E: none(waiver:finite-cyclic-face-incidence)
   anchors: []
   utility: none
   digest: Balanced directed transitions and path-end parity on a colored normal edge circle. -/

import D5.S3.Geometry.Hyperideal.FaceSignaturePropagation
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.EdgeStarTransitions

open D5.S3.Geometry.Hyperideal.FaceSignatureBalance
open D5.S3.Geometry.Hyperideal.FaceSignaturePropagation

/-- Local order (12,13,14,34,24,23), using vertices 0 through 3. -/
def edgeVertices : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2)]

/-- The two faces meeting each local edge, listed by omitted vertex. -/
def edgeFaces : Fin 6 → Fin 4 × Fin 4 :=
  ![(2, 3), (1, 3), (1, 2), (0, 1), (0, 2), (0, 3)]

def colorCard (low : Fin 6 → Bool) (e : Fin 6) : ℕ :=
  ∑ j : Fin 6, if low j = low e then 1 else 0

def colorDegree (low : Fin 6 → Bool) (e : Fin 6) (v : Fin 4) : ℕ :=
  ∑ j : Fin 6,
    if low j = low e ∧ ((edgeVertices j).1 = v ∨ (edgeVertices j).2 = v)
    then 1 else 0

/-- An end edge of the three-edge path in its own color. -/
def isPathEnd (low : Fin 6 → Bool) (e : Fin 6) : Prop :=
  colorCard low e = 3 ∧
    (colorDegree low e (edgeVertices e).1 = 1 ∨
      colorDegree low e (edgeVertices e).2 = 1)

/-- Exactly the face-signature condition of the M, P4, C local family. -/
def allowed (low : Fin 6 → Bool) : Prop :=
  ∀ f : Fin 4, faceLowCount low f = 1 ∨ faceLowCount low f = 2

instance (low : Fin 6 → Bool) : Decidable (allowed low) := by
  unfold allowed
  infer_instance

instance (low : Fin 6 → Bool) (e : Fin 6) : Decidable (isPathEnd low e) := by
  unfold isPathEnd
  infer_instance

abbrev Occurrence (T : Type*) := T × Fin 6

def incomingFace {T : Type*} (reversed : Occurrence T → Bool)
    (i : Occurrence T) : Fin 4 :=
  if reversed i then (edgeFaces i.2).2 else (edgeFaces i.2).1

def outgoingFace {T : Type*} (reversed : Occurrence T → Bool)
    (i : Occurrence T) : Fin 4 :=
  if reversed i then (edgeFaces i.2).1 else (edgeFaces i.2).2

/-- Slots of a local edge in its first and second incident faces. -/
def edgeFaceSlots : Fin 6 → Fin 3 × Fin 3 :=
  ![(0, 0), (0, 1), (1, 1), (0, 2), (1, 2), (2, 2)]

def outgoingSlot {T : Type*} (reversed : Occurrence T → Bool)
    (i : Occurrence T) : Fin 3 :=
  if reversed i then (edgeFaceSlots i.2).1 else (edgeFaceSlots i.2).2

def rawNext {T : Type*} (facePair : Equiv.Perm (T × Fin 4))
    (faceMap : T × Fin 4 → Fin 3 ≃ Fin 3)
    (reversed : Occurrence T → Bool) (i : Occurrence T) : Occurrence T :=
  let sourceFace : T × Fin 4 := (i.1, outgoingFace reversed i)
  let targetFace := facePair sourceFace
  (targetFace.1, faceEdge targetFace.2 (faceMap sourceFace (outgoingSlot reversed i)))

/-- Each local edge occurrence has two incident faces. The oriented edge links
identify its outgoing face with the incoming face of the next occurrence. -/
structure EdgeStars (T Edge : Type*) where
  edgeLabel : T → Fin 6 → Edge
  color : Edge → Bool
  reversed : Occurrence T → Bool
  valid : ∀ i : Occurrence T, allowed (fun j => color (edgeLabel i.1 j))
  facePair : Equiv.Perm (T × Fin 4)
  faceMap : T × Fin 4 → Fin 3 ≃ Fin 3
  faceLabels : ∀ (x : T × Fin 4) (n : Fin 3),
    edgeLabel x.1 (faceEdge x.2 n) =
      edgeLabel (facePair x).1 (faceEdge (facePair x).2 (faceMap x n))
  entersFace : ∀ i : Occurrence T,
    incomingFace reversed (rawNext facePair faceMap reversed i) =
      (facePair (i.1, outgoingFace reversed i)).2

/-- The face pairing induces a permutation of all local edge occurrences. -/
noncomputable def EdgeStars.next {T Edge : Type*} [Fintype T] (s : EdgeStars T Edge) :
    Equiv.Perm (Occurrence T) := by
  let f := rawNext s.facePair s.faceMap s.reversed
  have hslotTable (j : Fin 6) (b : Bool) :
      faceEdge (if b then (edgeFaces j).1 else (edgeFaces j).2)
        (if b then (edgeFaceSlots j).1 else (edgeFaceSlots j).2) = j := by
    cases b <;> fin_cases j <;> decide
  have hslot (i : Occurrence T) :
      faceEdge (outgoingFace s.reversed i) (outgoingSlot s.reversed i) = i.2 := by
    simpa [outgoingFace, outgoingSlot] using hslotTable i.2 (s.reversed i)
  have hfaceInjective (a : Fin 4) : Function.Injective (faceEdge a) := by
    fin_cases a <;> decide
  have hinj : Function.Injective f := by
    intro i j hij
    have hpaired :
        s.facePair (i.1, outgoingFace s.reversed i) =
          s.facePair (j.1, outgoingFace s.reversed j) := by
      apply Prod.ext
      · simpa [f, rawNext] using congrArg (fun x : Occurrence T => x.1) hij
      · calc
          (s.facePair (i.1, outgoingFace s.reversed i)).2 =
              incomingFace s.reversed (f i) := (s.entersFace i).symm
          _ = incomingFace s.reversed (f j) := congrArg _ hij
          _ = (s.facePair (j.1, outgoingFace s.reversed j)).2 := s.entersFace j
    have hsource := s.facePair.injective hpaired
    have hmapped :
        s.faceMap (i.1, outgoingFace s.reversed i) (outgoingSlot s.reversed i) =
          s.faceMap (i.1, outgoingFace s.reversed i) (outgoingSlot s.reversed j) := by
      apply hfaceInjective (s.facePair (i.1, outgoingFace s.reversed i)).2
      have hedge := congrArg Prod.snd hij
      dsimp [f, rawNext] at hedge
      rw [← hsource] at hedge
      exact hedge
    have hslots := (s.faceMap (i.1, outgoingFace s.reversed i)).injective hmapped
    apply Prod.ext
    · exact congrArg (fun x : T × Fin 4 => x.1) hsource
    · calc
        i.2 = faceEdge (outgoingFace s.reversed i) (outgoingSlot s.reversed i) :=
          (hslot i).symm
        _ = faceEdge (outgoingFace s.reversed j) (outgoingSlot s.reversed j) := by
          have hf := congrArg (fun x : T × Fin 4 => x.2) hsource
          exact congrArg₂ faceEdge hf hslots
        _ = j.2 := hslot j
  exact Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩

def EdgeStars.globalEdge {T Edge : Type*} (s : EdgeStars T Edge)
    (i : Occurrence T) : Edge := s.edgeLabel i.1 i.2

def EdgeStars.localColor {T Edge : Type*} (s : EdgeStars T Edge)
    (i : Occurrence T) : Fin 6 → Bool := fun j => s.color (s.edgeLabel i.1 j)

def EdgeStars.incoming {T Edge : Type*} (s : EdgeStars T Edge)
    (i : Occurrence T) : Fin 4 := incomingFace s.reversed i

def EdgeStars.outgoing {T Edge : Type*} (s : EdgeStars T Edge)
    (i : Occurrence T) : Fin 4 := outgoingFace s.reversed i

/-- False codes face count one; true codes face count two. -/
def EdgeStars.signature {T Edge : Type*} (s : EdgeStars T Edge)
    (i : Occurrence T) : Bool :=
  decide (faceLowCount (s.localColor i) (s.incoming i) = 2)

def EdgeStars.Fiber {T Edge : Type*} (s : EdgeStars T Edge) (e : Edge) : Type _ :=
  {i : Occurrence T // s.globalEdge i = e}

noncomputable def EdgeStars.nextFiber {T Edge : Type*} [Fintype T] (s : EdgeStars T Edge) (e : Edge)
    (hpres : ∀ i, s.globalEdge (s.next i) = s.globalEdge i) :
    Equiv.Perm (s.Fiber e) where
  toFun i := ⟨s.next i.1, by
    rw [hpres i.1, i.2]⟩
  invFun i := ⟨s.next.symm i.1, by
    calc
      s.globalEdge (s.next.symm i.1) =
          s.globalEdge (s.next (s.next.symm i.1)) :=
        (hpres (s.next.symm i.1)).symm
      _ = s.globalEdge i.1 := by rw [s.next.apply_symm_apply]
      _ = e := i.2⟩
  left_inv := by intro i; apply Subtype.ext; simp
  right_inv := by intro i; apply Subtype.ext; simp

noncomputable def EdgeStars.rise {T Edge : Type*} [Fintype T] [DecidableEq Edge]
    (s : EdgeStars T Edge) (e : Edge) : ℕ :=
  by
    letI : Fintype (s.Fiber e) := Subtype.fintype _
    exact ∑ i : s.Fiber e,
      if s.signature i.1 = false ∧ s.signature (s.next i.1) = true then 1 else 0

noncomputable def EdgeStars.fall {T Edge : Type*} [Fintype T] [DecidableEq Edge]
    (s : EdgeStars T Edge) (e : Edge) : ℕ :=
  by
    letI : Fintype (s.Fiber e) := Subtype.fintype _
    exact ∑ i : s.Fiber e,
      if s.signature i.1 = true ∧ s.signature (s.next i.1) = false then 1 else 0

noncomputable def EdgeStars.ends {T Edge : Type*} [Fintype T] [DecidableEq Edge]
    (s : EdgeStars T Edge) (e : Edge) : ℕ :=
  by
    letI : Fintype (s.Fiber e) := Subtype.fintype _
    exact ∑ i : s.Fiber e, if s.signature i.1 ≠ s.signature (s.next i.1) then 1 else 0

noncomputable def EdgeStars.pathEndCount {T Edge : Type*} [Fintype T] [DecidableEq Edge]
    (s : EdgeStars T Edge) (e : Edge) : ℕ :=
  by
    letI : Fintype (s.Fiber e) := Subtype.fintype _
    exact ∑ i : s.Fiber e, if isPathEnd (s.localColor i.1) i.1.2 then 1 else 0

/-- On every global edge, the two directed face-signature transitions have
equal multiplicity, and own-color P4 path ends occur an even number of times. -/
private theorem oriented_edge_balance {T Edge : Type*} [Fintype T] [DecidableEq Edge]
    (s : EdgeStars T Edge) (e : Edge) :
    s.rise e = s.fall e ∧ Even (s.pathEndCount e) := by
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
  have hlocal (low : Fin 6 → Bool) (e : Fin 6) (h : allowed low) :
      isPathEnd low e ↔
        faceLowCount low (edgeFaces e).1 ≠ faceLowCount low (edgeFaces e).2 := by
    have hbits : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ j : Fin 6,
        allowed ![b0, b1, b2, b3, b4, b5] →
        (isPathEnd ![b0, b1, b2, b3, b4, b5] j ↔
          faceLowCount ![b0, b1, b2, b3, b4, b5] (edgeFaces j).1 ≠
            faceLowCount ![b0, b1, b2, b3, b4, b5] (edgeFaces j).2) := by
      intro b0 b1 b2 b3 b4 b5 j
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
        cases b4 <;> cases b5 <;> fin_cases j <;> decide
    have hvec : ![low 0, low 1, low 2, low 3, low 4, low 5] = low := by
      funext i
      fin_cases i <;> rfl
    rw [← hvec] at h ⊢
    exact hbits (low 0) (low 1) (low 2) (low 3) (low 4) (low 5) e h
  have hbalance (q : s.Fiber e → Bool) (shift : Equiv.Perm (s.Fiber e)) :
      (∑ i : s.Fiber e, if q i = false ∧ q (shift i) = true then 1 else 0) =
        (∑ i : s.Fiber e, if q i = true ∧ q (shift i) = false then 1 else 0) ∧
      Even (∑ i : s.Fiber e, if q i ≠ q (shift i) then 1 else 0) := by
    have hshift :
        (∑ i : s.Fiber e, (q (shift i)).toNat) =
          ∑ i : s.Fiber e, (q i).toNat := by
      simpa using (Equiv.sum_comp shift (fun i => (q i).toNat))
    have hstep (i : s.Fiber e) :
        (if q i = false ∧ q (shift i) = true then 1 else 0) + (q i).toNat =
          (if q i = true ∧ q (shift i) = false then 1 else 0) +
            (q (shift i)).toNat := by
      cases q i <;> cases q (shift i) <;> simp
    have hsum := Finset.sum_congr rfl
      (fun i (_ : i ∈ (Finset.univ : Finset (s.Fiber e))) => hstep i)
    simp only [Finset.sum_add_distrib] at hsum
    have heq :
        (∑ i : s.Fiber e, if q i = false ∧ q (shift i) = true then 1 else 0) =
          ∑ i : s.Fiber e, if q i = true ∧ q (shift i) = false then 1 else 0 := by
      omega
    have hsplit (i : s.Fiber e) :
        (if q i ≠ q (shift i) then 1 else 0) =
          (if q i = false ∧ q (shift i) = true then 1 else 0) +
            (if q i = true ∧ q (shift i) = false then 1 else 0) := by
      cases q i <;> cases q (shift i) <;> simp
    have hend := Finset.sum_congr rfl
      (fun i (_ : i ∈ (Finset.univ : Finset (s.Fiber e))) => hsplit i)
    simp only [Finset.sum_add_distrib] at hend
    refine ⟨heq, ?_⟩
    refine ⟨∑ i : s.Fiber e, if q i = false ∧ q (shift i) = true then 1 else 0, ?_⟩
    omega
  have hdiff (a b : ℕ) (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2) :
      (decide (a = 2) ≠ decide (b = 2)) ↔ a ≠ b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  have hface (i : Occurrence T) :
      isPathEnd (s.localColor i) i.2 ↔
        faceLowCount (s.localColor i) (s.incoming i) ≠
          faceLowCount (s.localColor i) (s.outgoing i) := by
    have h := hlocal (s.localColor i) i.2 (s.valid i)
    by_cases hr : s.reversed i = true
    · simpa [EdgeStars.incoming, EdgeStars.outgoing, incomingFace, outgoingFace, hr] using
        (show isPathEnd (s.localColor i) i.2 ↔
            faceLowCount (s.localColor i) (edgeFaces i.2).2 ≠
              faceLowCount (s.localColor i) (edgeFaces i.2).1 from
          ⟨fun he => (h.mp he).symm, fun he => h.mpr he.symm⟩)
    · have hr' : s.reversed i = false := Bool.eq_false_iff.mpr hr
      simpa [EdgeStars.incoming, EdgeStars.outgoing, incomingFace, outgoingFace, hr'] using h
  have hfaceSum (i : Occurrence T) (f : Fin 4) :
      faceLowCount (s.localColor i) f =
        ∑ n : Fin 3, (s.color (s.edgeLabel i.1 (faceEdge f n))).toNat := by
    fin_cases f <;> simp [faceLowCount, EdgeStars.localColor, faceEdge, Fin.sum_univ_three]
  have hmatch (i : Occurrence T) :
      faceLowCount (s.localColor i) (s.outgoing i) =
        faceLowCount (s.localColor (s.next i)) (s.incoming (s.next i)) := by
    let x : T × Fin 4 := (i.1, s.outgoing i)
    let p := s.faceMap x
    have htarget : s.facePair x = ((s.next i).1, s.incoming (s.next i)) := by
      apply Prod.ext
      · rfl
      · exact (s.entersFace i).symm
    have hp (n : Fin 3) :
        s.edgeLabel i.1 (faceEdge (s.outgoing i) n) =
          s.edgeLabel (s.next i).1 (faceEdge (s.incoming (s.next i)) (p n)) := by
      have h := s.faceLabels x n
      rw [htarget] at h
      exact h
    calc
      faceLowCount (s.localColor i) (s.outgoing i) =
          ∑ n : Fin 3, (s.color (s.edgeLabel i.1 (faceEdge (s.outgoing i) n))).toNat :=
        hfaceSum i (s.outgoing i)
      _ = ∑ n : Fin 3,
          (s.color (s.edgeLabel (s.next i).1
            (faceEdge (s.incoming (s.next i)) (p n)))).toNat := by
        apply Finset.sum_congr rfl
        intro n _
        rw [show s.edgeLabel i.1 (faceEdge (s.outgoing i) n) =
          s.edgeLabel (s.next i).1 (faceEdge (s.incoming (s.next i)) (p n)) from
          hp n]
      _ = ∑ n : Fin 3,
          (s.color (s.edgeLabel (s.next i).1
            (faceEdge (s.incoming (s.next i)) n))).toNat := by
        exact Equiv.sum_comp p (fun n : Fin 3 =>
          (s.color (s.edgeLabel (s.next i).1
            (faceEdge (s.incoming (s.next i)) n))).toNat)
      _ = faceLowCount (s.localColor (s.next i)) (s.incoming (s.next i)) :=
        (hfaceSum (s.next i) (s.incoming (s.next i))).symm
  have hnext (i : Occurrence T) :
      s.signature (s.next i) =
        decide (faceLowCount (s.localColor i) (s.outgoing i) = 2) := by
    change decide (faceLowCount (s.localColor (s.next i))
      (s.incoming (s.next i)) = 2) = _
    exact congrArg (fun m : ℕ => decide (m = 2)) (hmatch i).symm
  have hpath (i : Occurrence T) :
      isPathEnd (s.localColor i) i.2 ↔
        s.signature i ≠ s.signature (s.next i) := by
    rw [hnext i]
    exact (hface i).trans
      ((hdiff _ _ (s.valid i (s.incoming i)) (s.valid i (s.outgoing i))).symm)
  have hcount : s.pathEndCount e = s.ends e := by
    unfold EdgeStars.pathEndCount EdgeStars.ends
    apply Finset.sum_congr rfl
    intro i _
    simp only [hpath i.1]
  have hb := hbalance (fun i : s.Fiber e => s.signature i.1) (s.nextFiber e hpres)
  exact ⟨hb.1, hcount ▸ hb.2⟩

namespace FlagOrientation

private def faceSide : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![false, false, true],
    ![false, true, true], ![true, true, true]]

private def localFlagEquiv : Fin 4 × Fin 3 ≃ Fin 6 × Bool where
  toFun x := (faceEdge x.1 x.2, faceSide x.1 x.2)
  invFun x :=
    if x.2 then ((edgeFaces x.1).2, (edgeFaceSlots x.1).2)
    else ((edgeFaces x.1).1, (edgeFaceSlots x.1).1)
  left_inv := by
    intro x
    rcases x with ⟨f, n⟩
    fin_cases f <;> fin_cases n <;> decide
  right_inv := by
    intro x
    rcases x with ⟨j, b⟩
    fin_cases j <;> cases b <;> decide

private abbrev Flag (T : Type*) := T × (Fin 4 × Fin 3)

private def flagOcc {T : Type*} (d : Flag T) : Occurrence T :=
  (d.1, (localFlagEquiv d.2).1)

private def otherFace {T : Type*} : Equiv.Perm (Flag T) := by
  let e : Flag T ≃ T × (Fin 6 × Bool) :=
    Equiv.prodCongr (Equiv.refl T) localFlagEquiv
  let flip : Equiv.Perm (T × (Fin 6 × Bool)) :=
    Equiv.prodCongr (Equiv.refl T)
      (Equiv.prodCongr (Equiv.refl (Fin 6)) (Equiv.swap false true))
  exact e.trans (flip.trans e.symm)

private structure Pairing (T : Type*) where
  facePair : Equiv.Perm (T × Fin 4)
  faceMap : T × Fin 4 → Fin 3 ≃ Fin 3
  pairInvolutive : facePair * facePair = 1
  pairFixedFree : ∀ x, facePair x ≠ x
  mapInverse : ∀ x n, faceMap (facePair x) (faceMap x n) = n

private def Pairing.cross {T : Type*} (p : Pairing T) : Equiv.Perm (Flag T) := by
  let crossRaw (d : Flag T) : Flag T :=
    let x : T × Fin 4 := (d.1, d.2.1)
    let y := p.facePair x
    (y.1, (y.2, p.faceMap x d.2.2))
  have hcross (d : Flag T) : crossRaw (crossRaw d) = d := by
    rcases d with ⟨t, ⟨f, n⟩⟩
    have hpair : p.facePair (p.facePair (t, f)) = (t, f) := by
      have h := congrArg (fun e : Equiv.Perm (T × Fin 4) => e (t, f))
        p.pairInvolutive
      simpa using h
    have hmap := p.mapInverse (t, f) n
    simp only [crossRaw]
    rw [hpair, hmap]
  exact {
    toFun := crossRaw
    invFun := crossRaw
    left_inv := hcross
    right_inv := hcross
  }

variable {D : Type*} [Fintype D]

private theorem no_partner_in_same_cycle (a t : Equiv.Perm D)
    (ha : a * a = 1) (ht : t * t = 1)
    (ha_fixed : ∀ x, a x ≠ x) (ht_fixed : ∀ x, t x ≠ x) (x : D) :
    ¬(a * t).SameCycle x (t x) := by
  intro h
  let s := a * t
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have htt : t⁻¹ = t := by
    calc
      t⁻¹ = t⁻¹ * (t * t) := by rw [ht]; group
      _ = t := by group
  have hat : a⁻¹ = a := by
    calc
      a⁻¹ = a⁻¹ * (a * a) := by rw [ha]; group
      _ = a := by group
  have hconjBase : t * s * t = s⁻¹ := by
    dsimp [s]
    rw [mul_inv_rev, hat, htt]
    calc
      t * (a * t) * t = t * a * (t * t) := by group
      _ = t * a := by rw [ht]; group
  have hconj (k : ℕ) : t * s^k * t = (s⁻¹)^k := by
    calc
      t * s^k * t = (t * s * t)^k := by
        simpa [htt] using (conj_pow (a := t) (b := s) (i := k)).symm
      _ = (s⁻¹)^k := by rw [hconjBase]
  have hmove (k : ℕ) : t * s^k = (s⁻¹)^k * t := by
    calc
      t * s^k = (t * s^k * t) * t := by rw [mul_assoc, ht]; group
      _ = (s⁻¹)^k * t := by rw [hconj]
  have hrel : (s^n) x = t x := hn
  have hrem := Nat.mod_two_eq_zero_or_one n
  rcases hrem with heven | hodd
  · have hnum : n = 2 * (n / 2) := by omega
    let m := n / 2
    have hfix : t ((s^m) x) = (s^m) x := by
      change (t * s^m) x = _
      rw [hmove]
      change ((s⁻¹)^m) (t x) = _
      rw [← hrel]
      change (((s⁻¹)^m * s^n) x) = _
      rw [hnum]
      congr 1
      group
      congr 1
      dsimp [m]
      omega
    exact ht_fixed ((s^m) x) hfix
  · have hnum : n = 2 * (n / 2) + 1 := by omega
    let m := n / 2
    have has : a = s * t := by dsimp [s]; rw [mul_assoc, ht]; group
    have hfix : a ((s^(m+1)) x) = (s^(m+1)) x := by
      rw [has]
      change (s * t * s^(m+1)) x = _
      rw [mul_assoc, hmove]
      change (s * (s⁻¹)^(m+1)) (t x) = _
      rw [← hrel]
      change ((s * (s⁻¹)^(m+1) * s^n) x) = _
      rw [hnum]
      congr 1
      group
      congr 1
      dsimp [m]
      omega
    exact ha_fixed ((s^(m+1)) x) hfix

private theorem exists_flag_orientation (a t : Equiv.Perm D)
    (ha : a * a = 1) (ht : t * t = 1)
    (ha_fixed : ∀ x, a x ≠ x) (ht_fixed : ∀ x, t x ≠ x) :
    ∃ incoming : D → Prop,
      (∀ x, incoming (t x) ↔ ¬ incoming x) ∧
      (∀ x, incoming (a x) ↔ ¬ incoming x) := by
  let s := a * t
  let Q := Quotient (Equiv.Perm.SameCycle.setoid s)
  let q : D → Q := Quotient.mk _
  letI : Fintype Q := Fintype.ofFinite Q
  let rank : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let incoming : D → Prop := fun x => rank (q x) < rank (q (t x))
  have ht_apply (x : D) : t (t x) = x := by
    have h := congrArg (fun p : Equiv.Perm D => p x) ht
    simpa using h
  have hqne (x : D) : q x ≠ q (t x) := by
    intro h
    exact no_partner_in_same_cycle a t ha ht ha_fixed ht_fixed x
      (Quotient.exact h)
  have htt : t⁻¹ = t := by
    calc
      t⁻¹ = t⁻¹ * (t * t) := by rw [ht]; group
      _ = t := by group
  have hat : a⁻¹ = a := by
    calc
      a⁻¹ = a⁻¹ * (a * a) := by rw [ha]; group
      _ = a := by group
  have hconjBase : t * s * t = s⁻¹ := by
    dsimp [s]
    rw [mul_inv_rev, hat, htt]
    calc
      t * (a * t) * t = t * a * (t * t) := by group
      _ = t * a := by rw [ht]; group
  have hts : t * s = s⁻¹ * t := by
    calc
      t * s = (t * s * t) * t := by rw [mul_assoc, ht]; group
      _ = s⁻¹ * t := by rw [hconjBase]
  have hqs (x : D) : q (s x) = q x := by
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_apply_left).mpr (Equiv.Perm.SameCycle.refl s x)
  have hqt (x : D) : q (t (s x)) = q (t x) := by
    have heq : t (s x) = s.symm (t x) := by
      have h := congrArg (fun p : Equiv.Perm D => p x) hts
      simpa using h
    rw [heq]
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_symm_apply_left).mpr
      (Equiv.Perm.SameCycle.refl s (t x))
  have hs (x : D) : incoming (s x) ↔ incoming x := by
    simp only [incoming, hqs, hqt]
  have hswitch (x : D) : incoming (t x) ↔ ¬ incoming x := by
    have hne : rank (q x) ≠ rank (q (t x)) := rank.injective.ne (hqne x)
    simp only [incoming, ht_apply]
    omega
  have has : a = s * t := by dsimp [s]; rw [mul_assoc, ht]; group
  refine ⟨incoming, hswitch, ?_⟩
  intro x
  have hax : a x = s (t x) := by rw [has]; rfl
  rw [hax, hs, hswitch]

private def flagFor {T : Type*} (i : Occurrence T) (b : Bool) : Flag T :=
  (i.1, localFlagEquiv.symm (i.2, b))

private theorem Pairing.exists_reversed {T : Type*} [Fintype T] (p : Pairing T) :
    ∃ r : Occurrence T → Bool,
      ∀ i : Occurrence T,
        incomingFace r (rawNext p.facePair p.faceMap r i) =
          (p.facePair (i.1, outgoingFace r i)).2 := by
  classical
  have hotherInv : otherFace (T := T) * otherFace (T := T) = 1 := by
    apply Equiv.ext
    intro d
    rcases d with ⟨t, ⟨f, n⟩⟩
    fin_cases f <;> fin_cases n <;> simp [otherFace, localFlagEquiv, faceSide,
      edgeFaces, edgeFaceSlots, faceEdge]
  have hotherFixed (d : Flag T) : otherFace d ≠ d := by
    intro h
    have hside := congrArg (fun z : Flag T => (localFlagEquiv z.2).2) h
    rcases d with ⟨t, ⟨f, n⟩⟩
    fin_cases f <;> fin_cases n <;>
      simp [otherFace, localFlagEquiv, faceSide, edgeFaces, edgeFaceSlots, faceEdge]
        at hside
  have hcrossInv : p.cross * p.cross = 1 := by
    apply Equiv.ext
    intro d
    exact p.cross.left_inv d
  have hcrossFixed (d : Flag T) : p.cross d ≠ d := by
    intro h
    have hface := congrArg (fun z : Flag T => (z.1, z.2.1)) h
    have hp : p.facePair (d.1, d.2.1) = (d.1, d.2.1) := by
      simpa [Pairing.cross] using hface
    exact p.pairFixedFree (d.1, d.2.1) hp
  obtain ⟨inc, hswitch, hcross⟩ :=
    exists_flag_orientation p.cross otherFace hcrossInv hotherInv
      hcrossFixed hotherFixed
  have otherFace_flagFor (i : Occurrence T) (b : Bool) :
      otherFace (flagFor i b) = flagFor i (!b) := by
    rcases i with ⟨t, j⟩
    fin_cases j <;> cases b <;>
      simp [otherFace, flagFor, localFlagEquiv, faceSide,
        edgeFaces, edgeFaceSlots, faceEdge]
  have flagFor_outgoing (r : Occurrence T → Bool) (i : Occurrence T) :
      flagFor i (!r i) = (i.1, (outgoingFace r i, outgoingSlot r i)) := by
    rcases i with ⟨t, j⟩
    fin_cases j <;> cases h : r (t, _) <;>
      simp_all [flagFor, outgoingFace, outgoingSlot, localFlagEquiv,
        edgeFaces, edgeFaceSlots]
  have flagFor_incoming (r : Occurrence T → Bool) (i : Occurrence T) :
      (flagFor i (r i)).2.1 = incomingFace r i := by
    rcases i with ⟨t, j⟩
    fin_cases j <;> cases h : r (t, _) <;>
      simp_all [flagFor, incomingFace, localFlagEquiv, edgeFaces, edgeFaceSlots]
  have hcrossOcc (d : Flag T) :
      flagOcc (p.cross d) =
        let x : T × Fin 4 := (d.1, d.2.1)
        let y := p.facePair x
        (y.1, faceEdge y.2 (p.faceMap x d.2.2)) := by
    rfl
  let r : Occurrence T → Bool := fun i => decide (¬ inc (flagFor i false))
  have hr_false (i : Occurrence T) :
      r i = false ↔ inc (flagFor i false) := by
    simp [r]
  have hr_true (i : Occurrence T) :
      r i = true ↔ ¬ inc (flagFor i false) := by
    simp [r]
  have hin (i : Occurrence T) : inc (flagFor i (r i)) := by
    by_cases h : inc (flagFor i false)
    · have hr : r i = false := (hr_false i).mpr h
      simpa [hr] using h
    · have hr : r i = true := (hr_true i).mpr h
      have hflip := (hswitch (flagFor i false)).mpr h
      rw [otherFace_flagFor] at hflip
      simpa [hr] using hflip
  have hout (i : Occurrence T) : ¬ inc (flagFor i (!r i)) := by
    have h : ¬ inc (otherFace (flagFor i (r i))) := by
      intro hh
      exact ((hswitch _).mp hh) (hin i)
    rw [otherFace_flagFor] at h
    simpa using h
  have hselected (z : Flag T) (hz : inc z) :
      z = flagFor (flagOcc z) (r (flagOcc z)) := by
    let b := (localFlagEquiv z.2).2
    have hzflag : z = flagFor (flagOcc z) b := by
      rcases z with ⟨t, fn⟩
      simp [flagFor, flagOcc, b]
    cases hb : b
    · have hi : inc (flagFor (flagOcc z) false) := by
        rw [hzflag, hb] at hz
        exact hz
      have hr := (hr_false (flagOcc z)).mpr hi
      simpa [hb, hr] using hzflag
    · have hi : inc (flagFor (flagOcc z) true) := by
        rw [hzflag, hb] at hz
        exact hz
      have hnot : ¬ inc (flagFor (flagOcc z) false) := by
        have h := (hswitch (flagFor (flagOcc z) false)).mp
        rw [otherFace_flagFor] at h
        exact h hi
      have hr := (hr_true (flagOcc z)).mpr hnot
      simpa [hb, hr] using hzflag
  refine ⟨r, ?_⟩
  intro i
  let d := flagFor i (!r i)
  have htarget : inc (p.cross d) :=
    (hcross d).mpr (hout i)
  have hraw : flagOcc (p.cross d) = rawNext p.facePair p.faceMap r i := by
    rw [hcrossOcc d]
    dsimp [d]
    rw [flagFor_outgoing r i]
    rfl
  have hside := hselected (p.cross d) htarget
  rw [hraw] at hside
  rw [← hraw]
  calc
    incomingFace r (flagOcc (p.cross d)) =
        (flagFor (flagOcc (p.cross d)) (r (flagOcc (p.cross d)))).2.1 :=
      (flagFor_incoming r _).symm
    _ = (p.cross d).2.1 := by
      rw [hraw]
      exact congrArg (fun z : Flag T => z.2.1) hside.symm
    _ = (p.facePair (i.1, outgoingFace r i)).2 := by
      dsimp [d, Pairing.cross]
      rw [flagFor_outgoing r i]

end FlagOrientation

/-- A finite tetrahedral face pairing with exact three-slot transport and
global edge colors. No normal-circle orientation is supplied as data. -/
structure FacePairedTriangulation (T Edge : Type*) where
  edgeLabel : T → Fin 6 → Edge
  color : Edge → Bool
  valid : ∀ i : Occurrence T, allowed (fun j => color (edgeLabel i.1 j))
  facePair : Equiv.Perm (T × Fin 4)
  faceMap : T × Fin 4 → Fin 3 ≃ Fin 3
  pairInvolutive : facePair * facePair = 1
  pairFixedFree : ∀ x, facePair x ≠ x
  mapInverse : ∀ x n, faceMap (facePair x) (faceMap x n) = n
  faceLabels : ∀ (x : T × Fin 4) (n : Fin 3),
    edgeLabel x.1 (faceEdge x.2 n) =
      edgeLabel (facePair x).1 (faceEdge (facePair x).2 (faceMap x n))

/-- The two involutions on exact face-edge flags determine a consistent
normal-circle orientation, including self-gluings and repeated edge labels. -/
noncomputable def FacePairedTriangulation.edgeStars {T Edge : Type*} [Fintype T]
    (p : FacePairedTriangulation T Edge) : EdgeStars T Edge := by
  let pairing : FlagOrientation.Pairing T := {
    facePair := p.facePair
    faceMap := p.faceMap
    pairInvolutive := p.pairInvolutive
    pairFixedFree := p.pairFixedFree
    mapInverse := p.mapInverse
  }
  let r := Classical.choose pairing.exists_reversed
  have hr := Classical.choose_spec pairing.exists_reversed
  exact {
    edgeLabel := p.edgeLabel
    color := p.color
    reversed := r
    valid := p.valid
    facePair := p.facePair
    faceMap := p.faceMap
    faceLabels := p.faceLabels
    entersFace := hr
  }

noncomputable def FacePairedTriangulation.rise {T Edge : Type*}
    [Fintype T] [DecidableEq Edge] (p : FacePairedTriangulation T Edge) (e : Edge) : ℕ :=
  p.edgeStars.rise e

noncomputable def FacePairedTriangulation.fall {T Edge : Type*}
    [Fintype T] [DecidableEq Edge] (p : FacePairedTriangulation T Edge) (e : Edge) : ℕ :=
  p.edgeStars.fall e

noncomputable def FacePairedTriangulation.pathEndCount {T Edge : Type*}
    [Fintype T] [DecidableEq Edge] (p : FacePairedTriangulation T Edge) (e : Edge) : ℕ :=
  p.edgeStars.pathEndCount e

/-- Face-edge slot identifications determine actual global edges, with no
prior choice of edge labels or normal-circle orientation. -/
structure RawFacePairing (T : Type*) where
  facePair : Equiv.Perm (T × Fin 4)
  faceMap : T × Fin 4 → Fin 3 ≃ Fin 3
  pairInvolutive : facePair * facePair = 1
  pairFixedFree : ∀ x, facePair x ≠ x
  mapInverse : ∀ x n, faceMap (facePair x) (faceMap x n) = n

def RawFacePairing.edgeStep {T : Type*} (p : RawFacePairing T)
    (i j : Occurrence T) : Prop :=
  ∃ (x : T × Fin 4) (n : Fin 3),
    i = (x.1, faceEdge x.2 n) ∧
      j = ((p.facePair x).1,
        faceEdge (p.facePair x).2 (p.faceMap x n))

/-- An actual global edge is an equivalence class generated by paired
face-edge slots. -/
def RawFacePairing.GlobalEdge {T : Type*} (p : RawFacePairing T) : Type _ :=
  Quotient (Relation.EqvGen.setoid p.edgeStep)

def RawFacePairing.edgeLabel {T : Type*} (p : RawFacePairing T)
    (t : T) (j : Fin 6) : p.GlobalEdge :=
  Quotient.mk (Relation.EqvGen.setoid p.edgeStep) (t, j)

def RawFacePairing.ValidColoring {T : Type*} (p : RawFacePairing T)
    (color : p.GlobalEdge → Bool) : Prop :=
  ∀ i : Occurrence T, allowed (fun j => color (p.edgeLabel i.1 j))

def RawFacePairing.toFacePairedTriangulation {T : Type*} (p : RawFacePairing T)
    (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color) :
    FacePairedTriangulation T p.GlobalEdge where
  edgeLabel := p.edgeLabel
  color := color
  valid := valid
  facePair := p.facePair
  faceMap := p.faceMap
  pairInvolutive := p.pairInvolutive
  pairFixedFree := p.pairFixedFree
  mapInverse := p.mapInverse
  faceLabels := by
    intro x n
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ ⟨x, n, rfl, rfl⟩

noncomputable def RawFacePairing.rise {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color)
    (e : p.GlobalEdge) : ℕ := by
  classical
  exact (p.toFacePairedTriangulation color valid).rise e

noncomputable def RawFacePairing.fall {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color)
    (e : p.GlobalEdge) : ℕ := by
  classical
  exact (p.toFacePairedTriangulation color valid).fall e

noncomputable def RawFacePairing.pathEndCount {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color)
    (e : p.GlobalEdge) : ℕ := by
  classical
  exact (p.toFacePairedTriangulation color valid).pathEndCount e

/-- On each actual global edge of a finite face-paired tetrahedral system,
the one-to-two and two-to-one face-signature transitions balance, and
own-color path ends have even multiplicity. -/
theorem global_edge_balance {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color)
    (e : p.GlobalEdge) :
    p.rise color valid e = p.fall color valid e ∧
      Even (p.pathEndCount color valid e) := by
  classical
  exact oriented_edge_balance (p.toFacePairedTriangulation color valid).edgeStars e

#print axioms global_edge_balance

end D5.S3.Geometry.Hyperideal.EdgeStarTransitions
