/- GID: D5/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CriticalEdgeSignatureWord
   mirror-E: none(waiver:finite-cyclic-face-incidence)
   anchors: []
   utility: none
   digest: Critical six-occurrence edge stars have at most one two-count face signature. -/

import D5.S3.Geometry.Hyperideal.EdgeStarBudgetMatrix

set_option autoImplicit false

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open D5.S3.Geometry.Hyperideal.EdgeStarBudgetMatrix
open D5.S3.Geometry.Hyperideal.FaceSignatureBalance
open D5.S3.Geometry.Hyperideal.FaceSignaturePropagation

namespace D5.S3.Geometry.Hyperideal.CriticalEdgeSignatureWord

private theorem local_classification
    (low : Fin 6 → Bool) (j : Fin 6)
    (hallowed : allowed low) (hlow : low j = true)
    (hthree : 3 ≤ highNeighbourCount low j) :
    (highNeighbourCount low j = 4 ∧ colorCard low j = 2) ∨
      (highNeighbourCount low j = 3 ∧ isPathEnd low j) := by
  have hbits : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ k : Fin 6,
      allowed ![b0, b1, b2, b3, b4, b5] →
      (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) k = true →
      3 ≤ highNeighbourCount ![b0, b1, b2, b3, b4, b5] k →
      (highNeighbourCount ![b0, b1, b2, b3, b4, b5] k = 4 ∧
          colorCard ![b0, b1, b2, b3, b4, b5] k = 2) ∨
        (highNeighbourCount ![b0, b1, b2, b3, b4, b5] k = 3 ∧
          isPathEnd ![b0, b1, b2, b3, b4, b5] k) := by
    intro b0 b1 b2 b3 b4 b5 k
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      cases b4 <;> cases b5 <;> fin_cases k <;> decide
  have hvec : ![low 0, low 1, low 2, low 3, low 4, low 5] = low := by
    funext i
    fin_cases i <;> rfl
  rw [← hvec] at hallowed hlow hthree ⊢
  exact hbits (low 0) (low 1) (low 2) (low 3) (low 4) (low 5) j
    hallowed hlow hthree

noncomputable def edgeDegree {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℕ := by
  classical
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  exact Fintype.card (s.Fiber e)

noncomputable def fourHighCount {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℕ := by
  classical
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  exact ∑ i : s.Fiber e,
    if highNeighbourCount (s.localColor i.1) i.1.2 = 4 then 1 else 0

private theorem path_end_count_zero_or_two {T : Type*} [Fintype T]
    (p : RawFacePairing T)
    (color : p.GlobalEdge → Bool) (valid : p.ValidColoring color)
    (e : p.GlobalEdge) :
    let s := (p.toFacePairedTriangulation color valid).edgeStars
    color e = true →
    (∀ i : s.Fiber e,
      3 ≤ highNeighbourCount (s.localColor i.1) i.1.2) →
    edgeDegree s e = 6 →
    4 ≤ fourHighCount s e →
    p.pathEndCount color valid e = 0 ∨ p.pathEndCount color valid e = 2 := by
  dsimp only
  intro hlow hthree hdegree hfav
  classical
  let s := (p.toFacePairedTriangulation color valid).edgeStars
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  have hdegree' : Fintype.card (s.Fiber e) = 6 := by
    simpa [edgeDegree] using hdegree
  have hfav' : 4 ≤ (∑ i : s.Fiber e,
      if highNeighbourCount (s.localColor i.1) i.1.2 = 4 then 1 else 0) := by
    simpa [fourHighCount] using hfav
  have hclass (i : s.Fiber e) :
      (highNeighbourCount (s.localColor i.1) i.1.2 = 4 ∧
        colorCard (s.localColor i.1) i.1.2 = 2) ∨
      (highNeighbourCount (s.localColor i.1) i.1.2 = 3 ∧
        isPathEnd (s.localColor i.1) i.1.2) := by
    have hlocal : s.localColor i.1 i.1.2 = true := by
      change color (s.globalEdge i.1) = true
      rw [i.2]
      exact hlow
    exact local_classification (s.localColor i.1) i.1.2
      (s.valid i.1) hlocal (hthree i)
  have hpoint (i : s.Fiber e) :
      (if highNeighbourCount (s.localColor i.1) i.1.2 = 4 then 1 else 0) +
        (if isPathEnd (s.localColor i.1) i.1.2 then 1 else 0) = 1 := by
    rcases hclass i with ⟨hfour, hcard⟩ | ⟨hthree', hend⟩
    · change highNeighbourCount (s.localColor i.1) i.1.2 = 4 at hfour
      change colorCard (s.localColor i.1) i.1.2 = 2 at hcard
      have hnot : ¬isPathEnd (s.localColor i.1) i.1.2 := by
        intro he
        have hthreeCard := he.1
        omega
      simp only [if_pos hfour, if_neg hnot]
    · change highNeighbourCount (s.localColor i.1) i.1.2 = 3 at hthree'
      change isPathEnd (s.localColor i.1) i.1.2 at hend
      have hnot : highNeighbourCount (s.localColor i.1) i.1.2 ≠ 4 := by omega
      simp only [if_neg hnot, if_pos hend]
  have hsum := Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset (s.Fiber e))) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have hpath : s.pathEndCount e =
      ∑ i : s.Fiber e, if isPathEnd (s.localColor i.1) i.1.2 then 1 else 0 := rfl
  have hsum' :
      (∑ i : s.Fiber e,
        if highNeighbourCount (s.localColor i.1) i.1.2 = 4 then 1 else 0) +
          s.pathEndCount e = Fintype.card (s.Fiber e) := by
    simpa [hpath] using hsum
  have hle : s.pathEndCount e ≤ 2 := by omega
  have heven : Even (s.pathEndCount e) := by
    have h := (global_edge_balance p color valid e).2
    change Even (s.pathEndCount e) at h
    exact h
  rcases heven with ⟨k, hk⟩
  have hanswer : s.pathEndCount e = 0 ∨ s.pathEndCount e = 2 := by omega
  simpa [RawFacePairing.pathEndCount, FacePairedTriangulation.pathEndCount] using hanswer

noncomputable def twoFaceCount {T Edge : Type*} [Fintype T]
    (s : EdgeStars T Edge) (e : Edge) : ℕ := by
  classical
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  exact ∑ i : s.Fiber e, if s.signature i.1 then 1 else 0

private theorem two_face_count_le_one {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color) (e : p.GlobalEdge) :
    let s := (p.toFacePairedTriangulation color valid).edgeStars
    color e = true →
    (∀ i : s.Fiber e,
      3 ≤ highNeighbourCount (s.localColor i.1) i.1.2) →
    edgeDegree s e = 6 →
    4 ≤ fourHighCount s e →
    (∀ i : s.Fiber e,
      ¬(s.signature i.1 = true ∧ s.signature (s.next i.1) = true)) →
    twoFaceCount s e ≤ 1 := by
  dsimp only
  intro hlow hthree hdegree hfav hno
  classical
  let s := (p.toFacePairedTriangulation color valid).edgeStars
  letI : Fintype (s.Fiber e) := Subtype.fintype _
  have hpathBound : s.pathEndCount e ≤ 2 := by
    have h := path_end_count_zero_or_two p color valid e hlow hthree hdegree hfav
    change s.pathEndCount e = 0 ∨ s.pathEndCount e = 2 at h
    omega
  have hpath (z : Occurrence T) :
      isPathEnd (s.localColor z) z.2 ↔
        s.signature z ≠ s.signature (s.next z) :=
    (path_end_signature_and_next s z).1
  have hcount : s.pathEndCount e = s.ends e := by
    unfold EdgeStars.pathEndCount EdgeStars.ends
    apply Finset.sum_congr rfl
    intro i _
    simp only [hpath i.1]
  have hsplit (i : s.Fiber e) :
      (if s.signature i.1 ≠ s.signature (s.next i.1) then 1 else 0) =
        (if s.signature i.1 = false ∧ s.signature (s.next i.1) = true then 1 else 0) +
          (if s.signature i.1 = true ∧ s.signature (s.next i.1) = false then 1 else 0) := by
    cases s.signature i.1 <;> cases s.signature (s.next i.1) <;> simp
  have hsum := Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset (s.Fiber e))) => hsplit i)
  simp only [Finset.sum_add_distrib] at hsum
  have htotal : s.pathEndCount e = s.rise e + s.fall e := by
    rw [hcount]
    simpa [EdgeStars.ends, EdgeStars.rise, EdgeStars.fall] using hsum
  have hbalance : s.rise e = s.fall e := by
    simpa [RawFacePairing.rise, RawFacePairing.fall,
      FacePairedTriangulation.rise, FacePairedTriangulation.fall] using
      (global_edge_balance p color valid e).1
  have hfall : s.fall e ≤ 1 := by omega
  have hpoint (i : s.Fiber e) :
      (if s.signature i.1 then 1 else 0) =
        (if s.signature i.1 = true ∧ s.signature (s.next i.1) = false then 1 else 0) := by
    cases hc : s.signature i.1 <;> cases hn : s.signature (s.next i.1)
    · simp [hc, hn]
    · simp [hc, hn]
    · simp [hc, hn]
    · exact False.elim (hno i ⟨hc, hn⟩)
  have hsumTrue := Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset (s.Fiber e))) => hpoint i)
  change twoFaceCount s e = s.fall e at hsumTrue
  change twoFaceCount s e ≤ 1
  omega

/-- Under the critical six-edge star conditions, every occurrence is an
isolated low pair or a path end. The actual face-signature circle has no
two-to-two transition and at most one two-count face. -/
theorem critical_edge_signature_word {T : Type*} [Fintype T]
    (p : RawFacePairing T) (color : p.GlobalEdge → Bool)
    (valid : p.ValidColoring color) (e : p.GlobalEdge) :
    let s := (p.toFacePairedTriangulation color valid).edgeStars
    color e = true →
    (∀ i : s.Fiber e,
      3 ≤ highNeighbourCount (s.localColor i.1) i.1.2) →
    edgeDegree s e = 6 →
    4 ≤ fourHighCount s e →
    (∀ i : s.Fiber e,
      (highNeighbourCount (s.localColor i.1) i.1.2 = 4 ∧
        colorCard (s.localColor i.1) i.1.2 = 2) ∨
      (highNeighbourCount (s.localColor i.1) i.1.2 = 3 ∧
        isPathEnd (s.localColor i.1) i.1.2)) ∧
    (p.pathEndCount color valid e = 0 ∨ p.pathEndCount color valid e = 2) ∧
    (∀ i : s.Fiber e,
      ¬(s.signature i.1 = true ∧ s.signature (s.next i.1) = true)) ∧
    twoFaceCount s e ≤ 1 := by
  dsimp only
  intro hlow hthree hdegree hfav
  let s := (p.toFacePairedTriangulation color valid).edgeStars
  have hclass (i : s.Fiber e) :
      (highNeighbourCount (s.localColor i.1) i.1.2 = 4 ∧
        colorCard (s.localColor i.1) i.1.2 = 2) ∨
      (highNeighbourCount (s.localColor i.1) i.1.2 = 3 ∧
        isPathEnd (s.localColor i.1) i.1.2) := by
    have hlocal : s.localColor i.1 i.1.2 = true := by
      change color (s.globalEdge i.1) = true
      rw [i.2]
      exact hlow
    exact local_classification (s.localColor i.1) i.1.2
      (s.valid i.1) hlocal (hthree i)
  have hno : ∀ i : s.Fiber e,
      ¬(s.signature i.1 = true ∧ s.signature (s.next i.1) = true) := by
    intro i hboth
    have hlocalColor : s.localColor i.1 i.1.2 = true := by
      change color (s.globalEdge i.1) = true
      rw [i.2]
      exact hlow
    have hno : faceLowCount (s.localColor i.1) (edgeFaces i.1.2).1 ≠ 2 ∨
        faceLowCount (s.localColor i.1) (edgeFaces i.1.2).2 ≠ 2 := by
      have hbits : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ k : Fin 6,
          (![b0, b1, b2, b3, b4, b5] : Fin 6 → Bool) k = true →
          3 ≤ highNeighbourCount ![b0, b1, b2, b3, b4, b5] k →
          faceLowCount ![b0, b1, b2, b3, b4, b5] (edgeFaces k).1 ≠ 2 ∨
            faceLowCount ![b0, b1, b2, b3, b4, b5] (edgeFaces k).2 ≠ 2 := by
        intro b0 b1 b2 b3 b4 b5 k
        cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
          cases b4 <;> cases b5 <;> fin_cases k <;> decide
      have hvec : ![(s.localColor i.1) 0, (s.localColor i.1) 1,
          (s.localColor i.1) 2, (s.localColor i.1) 3,
          (s.localColor i.1) 4, (s.localColor i.1) 5] = s.localColor i.1 := by
        funext k
        fin_cases k <;> rfl
      rw [← hvec] at hlocalColor ⊢
      have hthree' := hthree i
      rw [← hvec] at hthree'
      exact hbits _ _ _ _ _ _ i.1.2 hlocalColor hthree'
    have hin : faceLowCount (s.localColor i.1) (s.incoming i.1) = 2 := by
      exact of_decide_eq_true hboth.1
    have hout : faceLowCount (s.localColor i.1) (s.outgoing i.1) = 2 := by
      have hnext := (path_end_signature_and_next s i.1).2
      rw [hnext] at hboth
      exact of_decide_eq_true hboth.2
    by_cases hr : s.reversed i.1 = true
    · have hin' : faceLowCount (s.localColor i.1) (edgeFaces i.1.2).2 = 2 := by
        simpa [EdgeStars.incoming, incomingFace, hr] using hin
      have hout' : faceLowCount (s.localColor i.1) (edgeFaces i.1.2).1 = 2 := by
        simpa [EdgeStars.outgoing, outgoingFace, hr] using hout
      exact hno.elim (fun h => h hout') (fun h => h hin')
    · have hr' : s.reversed i.1 = false := Bool.eq_false_iff.mpr hr
      have hin' : faceLowCount (s.localColor i.1) (edgeFaces i.1.2).1 = 2 := by
        simpa [EdgeStars.incoming, incomingFace, hr'] using hin
      have hout' : faceLowCount (s.localColor i.1) (edgeFaces i.1.2).2 = 2 := by
        simpa [EdgeStars.outgoing, outgoingFace, hr'] using hout
      exact hno.elim (fun h => h hin') (fun h => h hout')
  exact ⟨hclass,
    path_end_count_zero_or_two p color valid e hlow hthree hdegree hfav,
    hno,
    two_face_count_le_one p color valid e hlow hthree hdegree hfav hno⟩

#print axioms critical_edge_signature_word

end D5.S3.Geometry.Hyperideal.CriticalEdgeSignatureWord
