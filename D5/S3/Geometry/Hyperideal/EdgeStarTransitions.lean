/- GID: D5/S3/Geometry/Hyperideal/EdgeStarTransitions
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/EdgeStarTransitions
   mirror-E: none(waiver:finite-cyclic-face-incidence)
   anchors: []
   utility: none
   digest: Balanced directed transitions and path-end parity on a colored normal edge circle. -/
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Geometry.Hyperideal.EdgeStarTransitions
def faceLowCount (low : Fin 6 → Bool) : Fin 4 → ℕ :=
  ![(low 3).toNat + (low 4).toNat + (low 5).toNat,
    (low 1).toNat + (low 2).toNat + (low 3).toNat,
    (low 0).toNat + (low 2).toNat + (low 4).toNat,
    (low 0).toNat + (low 1).toNat + (low 5).toNat]
def faceEdge : Fin 4 → Fin 3 → Fin 6 :=
  ![![3, 4, 5], ![1, 2, 3], ![0, 2, 4], ![0, 1, 5]]
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
/-- Local path ends are exactly signature changes. Face-slot gluing
carries each outgoing signature to the next incoming one. -/
theorem path_end_signature_and_next {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (i : Occurrence T) :
    (isPathEnd (s.localColor i) i.2 ↔ s.signature i ≠ s.signature (s.next i)) ∧
    s.signature (s.next i) =
      decide (faceLowCount (s.localColor i) (s.outgoing i) = 2) := by
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
  exact ⟨hpath i, hnext i⟩
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
  have hpath (i : Occurrence T) :
      isPathEnd (s.localColor i) i.2 ↔
        s.signature i ≠ s.signature (s.next i) :=
    (path_end_signature_and_next s i).1
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
private def flagFor {T : Type*} (i : Occurrence T) (b : Bool) : Flag T :=
  (i.1, localFlagEquiv.symm (i.2, b))
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
open FlagOrientation in
set_option maxHeartbeats 2000000 in
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
  /-
  Copyright (c) 2026 William Whistler. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: William Whistler

  Adapted from RS.EdgeSubset.TransitionSystem.pairing_not_sameCycle and
  RS.EdgeSubset.TransitionSystem.buildOrientation in
  LeanPool/RegtsSevenster/RS/Novel/Skein/TransitionExists.lean,
  Vilin97/lean-pool at 762dd054ea9168a4aba93ae86b536b1bd841ce66.
  The adapted proof uses the actual face-edge flags and the walk
  pairing.cross * otherFace. The full Apache-2.0 LICENSE and applicable
  attribution notices are in Library/Geometry/whistler2026existence.md.
  -/
  let orientation : ∃ r : Occurrence T → Bool,
      ∀ i : Occurrence T,
        incomingFace r (rawNext pairing.facePair pairing.faceMap r i) =
          (pairing.facePair (i.1, outgoingFace r i)).2 := by
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
    have hcrossInv : pairing.cross * pairing.cross = 1 := by
      apply Equiv.ext
      intro d
      exact pairing.cross.left_inv d
    have hcrossFixed (d : Flag T) : pairing.cross d ≠ d := by
      intro h
      have hface := congrArg (fun z : Flag T => (z.1, z.2.1)) h
      have hp : pairing.facePair (d.1, d.2.1) = (d.1, d.2.1) := by
        simpa [Pairing.cross] using hface
      exact pairing.pairFixedFree (d.1, d.2.1) hp
    have hotherInv' : (otherFace (T := T))⁻¹ = otherFace := by
      calc
        (otherFace (T := T))⁻¹ = otherFace⁻¹ * (otherFace * otherFace) := by
          rw [hotherInv]
          group
        _ = otherFace := by group
    have hcrossInv' : pairing.cross⁻¹ = pairing.cross := by
      calc
        pairing.cross⁻¹ = pairing.cross⁻¹ * (pairing.cross * pairing.cross) := by
          rw [hcrossInv]
          group
        _ = pairing.cross := by group
    let walk : Equiv.Perm (Flag T) := pairing.cross * otherFace
    have hwalk_no_partner (d : Flag T) :
        ¬ walk.SameCycle d (otherFace d) := by
      intro hsame
      obtain ⟨m, hm_pos, _, hm_eq⟩ := hsame.exists_pow_eq''
      have hconjBase : otherFace * walk * otherFace = walk⁻¹ := by
        dsimp [walk]
        rw [mul_inv_rev, hotherInv', hcrossInv']
        calc
          otherFace * (pairing.cross * otherFace) * otherFace =
              otherFace * pairing.cross * (otherFace * otherFace) := by group
          _ = otherFace * pairing.cross := by rw [hotherInv]; group
      have hconj_zpow (n : ℤ) :
          otherFace * walk ^ n * otherFace = walk ^ (-n) := by
        calc
          otherFace * walk ^ n * otherFace =
              otherFace * walk ^ n * otherFace⁻¹ := by
                rw [hotherInv']
          _ = (MulAut.conj otherFace) (walk ^ n) := rfl
          _ = ((MulAut.conj otherFace) walk) ^ n :=
            map_zpow (MulAut.conj otherFace).toMonoidHom walk n
          _ = walk⁻¹ ^ n := by
            change (otherFace * walk * otherFace⁻¹) ^ n = walk⁻¹ ^ n
            rw [hotherInv', hconjBase]
          _ = walk ^ (-n) := inv_zpow' walk n
      have hconj_applied : ∀ n : ℤ,
          otherFace ((walk ^ n) (otherFace d)) = (walk ^ (-n)) d := by
        intro n
        have h := congr_fun (congr_arg DFunLike.coe (hconj_zpow n)) d
        simpa only [Equiv.Perm.mul_apply] using h
      have hm' : (walk ^ (m : ℤ)) d = otherFace d := by
        rw [zpow_natCast]
        exact hm_eq
      have hshift : ∀ n : ℤ,
          otherFace ((walk ^ (n + (m : ℤ))) d) = (walk ^ (-n)) d := by
        intro n
        rw [zpow_add, Equiv.Perm.mul_apply, hm']
        exact hconj_applied n
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · have key := hshift (-(j : ℤ))
        have harith : -(j : ℤ) + (m : ℤ) = (j : ℤ) := by omega
        rw [harith, neg_neg] at key
        have hval := congrArg id key
        exact hotherFixed _ hval
      · have key := hshift (-(j : ℤ))
        have harith : -(j : ℤ) + (m : ℤ) = (j : ℤ) + 1 := by omega
        rw [harith, neg_neg] at key
        set g := (walk ^ (j : ℤ)) d
        have hval : otherFace (walk g) = g := by
          simpa only [g, add_comm (j : ℤ) 1, zpow_add, zpow_one,
            Equiv.Perm.mul_apply] using key
        have hval2 : walk g = otherFace g := by
          have hdouble (z : Flag T) : otherFace (otherFace z) = z := by
            have h := congrArg (fun e : Equiv.Perm (Flag T) => e z) hotherInv
            simpa using h
          have h := congrArg otherFace hval
          rw [hdouble] at h
          exact h
        have hfixed : pairing.cross (otherFace g) = otherFace g := by
          simpa [walk, Equiv.Perm.mul_apply] using hval2
        exact hcrossFixed _ hfixed
    let flagFin : Flag T ≃ Fin (Fintype.card (Flag T)) := Fintype.equivFin (Flag T)
    letI : LinearOrder (Flag T) :=
      LinearOrder.lift' flagFin flagFin.injective
    let orbitOf (x : Flag T) : Finset (Flag T) :=
      Finset.univ.filter (fun y => walk.SameCycle x y)
    have orbit_nonempty (x : Flag T) : (orbitOf x).Nonempty :=
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.rfl⟩⟩
    let orbitMin (x : Flag T) : Flag T :=
      (orbitOf x).min' (orbit_nonempty x)
    have orbitMin_eq (x y : Flag T) (h : walk.SameCycle x y) :
        orbitMin x = orbitMin y := by
      simp only [orbitMin]
      congr 1
      ext z
      simp only [orbitOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
    have orbitMin_pairing_ne (x : Flag T) :
        orbitMin (otherFace x) ≠ orbitMin x := by
      intro heq
      have hmin_in_x : orbitMin x ∈ orbitOf x := Finset.min'_mem _ _
      have hmin_in_σx : orbitMin (otherFace x) ∈ orbitOf (otherFace x) :=
        Finset.min'_mem _ _
      rw [heq] at hmin_in_σx
      simp only [orbitOf, Finset.mem_filter, Finset.mem_univ, true_and]
        at hmin_in_x hmin_in_σx
      exact hwalk_no_partner x (hmin_in_x.trans hmin_in_σx.symm)
    have orbitMin_cross (x : Flag T) :
        orbitMin (pairing.cross x) = orbitMin (otherFace x) := by
      apply orbitMin_eq
      refine ⟨(-1 : ℤ), ?_⟩
      have hcrossSquare : pairing.cross (pairing.cross x) = x := by
        have h := congrArg (fun e : Equiv.Perm (Flag T) => e x) hcrossInv
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
      simpa only [zpow_neg_one, walk, mul_inv_rev, hotherInv', hcrossInv',
        Equiv.Perm.mul_apply] using congrArg otherFace hcrossSquare
    have orbitMin_other_cross (x : Flag T) :
        orbitMin (otherFace (pairing.cross x)) = orbitMin x := by
      apply orbitMin_eq
      refine ⟨(1 : ℤ), ?_⟩
      have hotherSquare : otherFace (otherFace (pairing.cross x)) = pairing.cross x := by
        have h := congrArg (fun e : Equiv.Perm (Flag T) => e (pairing.cross x)) hotherInv
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
      have hcrossSquare : pairing.cross (pairing.cross x) = x := by
        have h := congrArg (fun e : Equiv.Perm (Flag T) => e x) hcrossInv
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
      simpa only [zpow_one, walk, Equiv.Perm.mul_apply, hotherSquare] using hcrossSquare
    let isOut (g : Flag T) : Bool :=
      decide (orbitMin (otherFace g) < orbitMin g)
    have hcross_flip (g : Flag T) : isOut (pairing.cross g) = !isOut g := by
      simp only [isOut, orbitMin_other_cross, orbitMin_cross]
      rcases lt_or_gt_of_ne (Ne.symm (orbitMin_pairing_ne g)) with h | h
      · simp [h, not_lt_of_ge (le_of_lt h)]
      · simp [h, not_lt_of_ge (le_of_lt h)]
    have hpairing_flip (g : Flag T) : isOut (otherFace g) = !isOut g := by
      simp only [isOut]
      have hdouble : otherFace (otherFace g) = g := by
        have h := congrArg (fun e : Equiv.Perm (Flag T) => e g) hotherInv
        simpa using h
      rw [hdouble]
      rcases lt_or_gt_of_ne (Ne.symm (orbitMin_pairing_ne g)) with h | h
      · simp [h, not_lt_of_ge (le_of_lt h)]
      · simp [h, not_lt_of_ge (le_of_lt h)]
    let inc : Flag T → Prop := fun g => isOut g = true
    have hinc_cross (g : Flag T) : inc (pairing.cross g) ↔ ¬ inc g := by
      simp only [inc, hcross_flip]
      cases h : isOut g <;> simp [h]
    have hinc_pairing (g : Flag T) : inc (otherFace g) ↔ ¬ inc g := by
      simp only [inc, hpairing_flip]
      cases h : isOut g <;> simp [h]
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
        flagOcc (pairing.cross d) =
          let x : T × Fin 4 := (d.1, d.2.1)
          let y := pairing.facePair x
          (y.1, faceEdge y.2 (pairing.faceMap x d.2.2)) := by
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
        have hflip := (hinc_pairing (flagFor i false)).mpr h
        rw [otherFace_flagFor] at hflip
        simpa [hr] using hflip
    have hout (i : Occurrence T) : ¬ inc (flagFor i (!r i)) := by
      have h : ¬ inc (otherFace (flagFor i (r i))) := by
        intro hh
        exact (hinc_pairing _).mp hh (hin i)
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
          have h := (hinc_pairing (flagFor (flagOcc z) false)).mp
          rw [otherFace_flagFor] at h
          exact h hi
        have hr := (hr_true (flagOcc z)).mpr hnot
        simpa [hb, hr] using hzflag
    refine ⟨r, ?_⟩
    intro i
    let d := flagFor i (!r i)
    have htarget : inc (pairing.cross d) := (hinc_cross d).mpr (hout i)
    have hraw : flagOcc (pairing.cross d) = rawNext pairing.facePair pairing.faceMap r i := by
      rw [hcrossOcc d]
      dsimp [d]
      rw [flagFor_outgoing r i]
      rfl
    have hside := hselected (pairing.cross d) htarget
    rw [hraw] at hside
    rw [← hraw]
    calc
      incomingFace r (flagOcc (pairing.cross d)) =
          (flagFor (flagOcc (pairing.cross d)) (r (flagOcc (pairing.cross d)))).2.1 :=
        (flagFor_incoming r _).symm
      _ = (pairing.cross d).2.1 := by
        rw [hraw]
        exact congrArg (fun z : Flag T => z.2.1) hside.symm
      _ = (pairing.facePair (i.1, outgoingFace r i)).2 := by
        dsimp [d, Pairing.cross]
        rw [flagFor_outgoing r i]
  let r := Classical.choose orientation
  have hr := Classical.choose_spec orientation
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
