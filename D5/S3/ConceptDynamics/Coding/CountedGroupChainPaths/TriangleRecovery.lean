/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupChainPaths/TriangleRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both actual boundary triangles and the two sweep orders recover the same array. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths.PrescribedArrays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths

open CountedGroupOverlap
open RectangularNilpotenceBarrier

universe u
variable {H : Type u} [Group H] [Fintype H]

attribute [local irreducible] layerSweep localSweep

/-- Read the literal diagonal v_0^(L-1),v_1^(L-2),...,v_(L-1)^0 as the actual S path. -/

noncomputable def arrayMiddlePath [LinearOrder H] : {L : ℕ} → {data : IndexedChain H L} →
    (g : G34Array data L) → FactorPath (backwardFactors (toChain data))
      ((g.row (Fin.last L)).vertex 0) ((g.row 0).vertex (Fin.last L))
  | 0, _data, g => nilPath ((g.row 0).vertex 0)
  | L + 1, data, g => by
    have v : At (data.V 0) ((g.row 1).vertex (Fin.last L).castSucc)
        ((g.row 0).vertex (Fin.last (L + 1))) :=
      congrArg (fun r : NumberedRow (data.A 1) (L + 1) => r.vertex (Fin.last L).castSucc) (g.nextRow 0) ▸ (g.step 0).v (Fin.last L)
    exact (pathSnocEquiv (backwardFactors (toChain (tail data))) (data.V 0) _ _).symm
      ⟨(g.row 1).vertex (Fin.last L).castSucc,
        arrayMiddlePath (arrayPrefix (arrayTail g)), v⟩

attribute [local irreducible] peelRow orderedAtEquiv

/-- Peeling reads the same upper triangle, without using the outer right U edge. -/
theorem g34_peelRow [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (r : NumberedRow (U * V) (l + 1))
    (p : G34Step (U * V) (V * U) U V rfl rfl r) :
    peelRow U V l (r.vertex 0) (r.vertex (Fin.last (l + 1)))
      (rowWord (U * V) (l + 1) r) =
      ⟨p.next.vertex 0, p.next.vertex (Fin.last l).castSucc, p.u 0,
        rowWord (V * U) l (rowPrefix p.next), p.v (Fin.last l)⟩ := by
  induction l with
  | zero =>
    let pack (q : Σ y : Fin k, At U (r.vertex 0) y × At V y (r.vertex 1)) :=
      (⟨q.1, q.1, q.2.1, nilPath q.1, q.2.2⟩ : PeelBoundary U V 0 (r.vertex 0) (r.vertex 1))
    have ht := p.theta 0
    change orderedAtEquiv U V _ _ (r.edge 0) = ⟨p.next.vertex 0, p.u 0, p.v 0⟩ at ht
    conv_lhs => unfold peelRow
    change pack (orderedAtEquiv U V _ _ (r.edge 0)) = _
    exact congrArg pack ht
  | succ l ih =>
    let finish (q : Σ y : Fin k, At U (r.vertex 0) y × At V y (r.vertex 1))
        (t : PeelBoundary U V l (r.vertex 1) (r.vertex (Fin.last (l + 2)))) :
        PeelBoundary U V (l + 1) (r.vertex 0) (r.vertex (Fin.last (l + 2))) :=
      let b := (orderedAtEquiv V U q.1 t.1).symm ⟨r.vertex 1, q.2.2, t.2.2.1⟩
      ⟨q.1, t.2.1, q.2.1, ⟨t.1, b.1, b.2, t.2.2.2.1⟩, t.2.2.2.2⟩
    have hpeel {n k : ℕ}
        (U : GroupMat H n k) (V : GroupMat H k n) (l : ℕ) (i x j : Fin n)
        (a : At (U * V) i x) (w : Word (U * V) (l + 1) x j) :
        let q := orderedAtEquiv U V i x a
        let t := peelRow U V l x j w
        let b := (orderedAtEquiv V U q.1 t.1).symm ⟨x, q.2.2, t.2.2.1⟩
        peelRow U V (l + 1) i j ⟨x, a.1, a.2, w⟩ =
          ⟨q.1, t.2.1, q.2.1,
            ⟨t.1, b.1, b.2, t.2.2.2.1⟩, t.2.2.2.2⟩ := by with_unfolding_all rfl
    have hs := hpeel U V l (r.vertex 0) (r.vertex 1)
      (r.vertex (Fin.last (l + 2))) (r.edge 0) (rowWord (U * V) (l + 1) (rowTail r))
    have ht := p.theta 0
    change orderedAtEquiv U V _ _ (r.edge 0) = ⟨p.next.vertex 0, p.u 0, p.v 0⟩ at ht
    have he := p.eta 0
    change p.next.edge 0 = (orderedAtEquiv V U _ _).symm
      ⟨r.vertex 1, p.v 0, p.u 1⟩ at he
    refine hs.trans ((congrArg (finish (orderedAtEquiv U V _ _ (r.edge 0)))
      (ih (rowTail r) (stepTail p))).trans ?_)
    let t := (⟨p.next.vertex 1, p.next.vertex (Fin.last (l + 1)).castSucc, p.u 1,
      rowWord (V * U) l (rowPrefix (rowTail p.next)), p.v (Fin.last (l + 1))⟩ :
        PeelBoundary U V l (r.vertex 1) (r.vertex (Fin.last (l + 2))))
    change finish (orderedAtEquiv U V _ _ (r.edge 0)) t = _
    refine (congrArg (fun q => finish q t) ht).trans ?_
    let append (b : At (V * U) (p.next.vertex 0) (p.next.vertex 1)) :
        PeelBoundary U V (l + 1) (r.vertex 0) (r.vertex (Fin.last (l + 2))) :=
      ⟨p.next.vertex 0, p.next.vertex (Fin.last (l + 1)).castSucc, p.u 0,
        ⟨p.next.vertex 1, b.1, b.2, rowWord (V * U) l (rowPrefix (rowTail p.next))⟩,
        p.v (Fin.last (l + 1))⟩
    exact congrArg append he.symm

/-- Reverse peeling reads V on the left and the prescribed U on the right of the same row. -/
theorem g34_reversePeelRow [LinearOrder H] {n k l : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) (r : NumberedRow (U * V) (l + 1))
    (p : G34Step (U * V) (V * U) U V rfl rfl r) :
    peelRow V U l (p.next.vertex 0) (p.next.vertex (Fin.last (l + 1)))
      (rowWord (V * U) (l + 1) p.next) =
      ⟨r.vertex 1, r.vertex (Fin.last (l + 1)), p.v 0,
        rowWord (U * V) l (rowTail r), p.u (Fin.last (l + 1))⟩ := by
  have split_first : orderedAtEquiv V U _ _ (p.next.edge 0) =
      ⟨r.vertex 1, p.v 0, p.u 1⟩ := by
    have he := p.eta 0
    change p.next.edge 0 = (orderedAtEquiv V U _ _).symm
      ⟨r.vertex 1, p.v 0, p.u 1⟩ at he
    exact (congrArg (orderedAtEquiv V U _ _) he).trans (Equiv.apply_symm_apply _ _)
  induction l with
  | zero =>
    let pack (q : Σ y : Fin n, At V (p.next.vertex 0) y × At U y (p.next.vertex 1)) :=
      (⟨q.1, q.1, q.2.1, nilPath q.1, q.2.2⟩ :
        PeelBoundary V U 0 (p.next.vertex 0) (p.next.vertex 1))
    conv_lhs => unfold peelRow
    change pack (orderedAtEquiv V U _ _ (p.next.edge 0)) = _
    exact congrArg pack split_first
  | succ l ih =>
    let finish (q : Σ y : Fin n, At V (p.next.vertex 0) y × At U y (p.next.vertex 1))
        (t : PeelBoundary V U l (p.next.vertex 1) (p.next.vertex (Fin.last (l + 2)))) :
        PeelBoundary V U (l + 1) (p.next.vertex 0) (p.next.vertex (Fin.last (l + 2))) :=
      let b := (orderedAtEquiv U V q.1 t.1).symm ⟨p.next.vertex 1, q.2.2, t.2.2.1⟩
      ⟨q.1, t.2.1, q.2.1, ⟨t.1, b.1, b.2, t.2.2.2.1⟩, t.2.2.2.2⟩
    have hpeel {n k : ℕ}
        (U : GroupMat H n k) (V : GroupMat H k n) (l : ℕ) (i x j : Fin n)
        (a : At (U * V) i x) (w : Word (U * V) (l + 1) x j) :
        let q := orderedAtEquiv U V i x a
        let t := peelRow U V l x j w
        let b := (orderedAtEquiv V U q.1 t.1).symm ⟨x, q.2.2, t.2.2.1⟩
        peelRow U V (l + 1) i j ⟨x, a.1, a.2, w⟩ =
          ⟨q.1, t.2.1, q.2.1,
            ⟨t.1, b.1, b.2, t.2.2.2.1⟩, t.2.2.2.2⟩ := by with_unfolding_all rfl
    have hs := hpeel V U l (p.next.vertex 0) (p.next.vertex 1)
      (p.next.vertex (Fin.last (l + 2))) (p.next.edge 0)
      (rowWord (V * U) (l + 1) (rowTail p.next))
    have split_tail : orderedAtEquiv V U _ _ (p.next.edge 1) =
        ⟨r.vertex 2, p.v 1, p.u 2⟩ := by
      have he := p.eta 1
      change p.next.edge 1 = (orderedAtEquiv V U _ _).symm
        ⟨r.vertex 2, p.v 1, p.u 2⟩ at he
      exact (congrArg (orderedAtEquiv V U _ _) he).trans (Equiv.apply_symm_apply _ _)
    refine hs.trans ((congrArg (finish (orderedAtEquiv V U _ _ (p.next.edge 0)))
      (ih (rowTail r) (stepTail p) split_tail)).trans ?_)
    let t := (⟨r.vertex 2, r.vertex (Fin.last (l + 2)), p.v 1,
      rowWord (U * V) l (rowTail (rowTail r)), p.u (Fin.last (l + 2))⟩ :
        PeelBoundary V U l (p.next.vertex 1) (p.next.vertex (Fin.last (l + 2))))
    change finish (orderedAtEquiv V U _ _ (p.next.edge 0)) t = _
    refine (congrArg (fun q => finish q t) split_first).trans ?_
    have ht := p.theta 1
    change orderedAtEquiv U V _ _ (r.edge 1) =
      ⟨p.next.vertex 1, p.u 1, p.v 1⟩ at ht
    have hj : (orderedAtEquiv U V _ _).symm ⟨p.next.vertex 1, p.u 1, p.v 1⟩ = r.edge 1 :=
      (congrArg (orderedAtEquiv U V _ _).symm ht.symm).trans (Equiv.symm_apply_apply _ _)
    let append (b : At (U * V) (r.vertex 1) (r.vertex 2)) :
        PeelBoundary V U (l + 1) (p.next.vertex 0) (p.next.vertex (Fin.last (l + 2))) :=
      ⟨r.vertex 1, r.vertex (Fin.last (l + 2)), p.v 0,
        ⟨r.vertex 2, b.1, b.2, rowWord (U * V) l (rowTail (rowTail r))⟩,
        p.u (Fin.last (l + 2))⟩
    exact congrArg append hj

#print axioms fiber_card
#print axioms edgePathEquiv
#print axioms cumulative_equations

private theorem rowFirst_zero [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i : Fin n) (j : Fin m) (r : FactorPath (forwardFactors c) i j) :
    rowFirst c 0 i j ⟨i, nilPath i, r⟩ = ⟨j, r, nilPath j⟩ := by
  induction c with
  | nil A =>
    rcases r with ⟨⟨v, hvi, hvj⟩⟩
    subst v
    subst j
    rfl
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    rcases r with ⟨z, u, cu, r⟩
    have hrow (l : ℕ) (i : Fin n) (j : Fin m)
        (x : Fin n) (w : Word (U * V) l i x) (z : Fin k)
        (u : H) (cu : Fin ((U x z).coeff u)) (r : FactorPath (forwardFactors c) z j) :
        rowFirst (.cons U V rfl rfl c) l i j ⟨x, w, ⟨z, u, cu, r⟩⟩ =
          let t := layerSweep U V l i z ⟨x, w, ⟨u, cu⟩⟩
          let q := rowFirst c l t.1 j ⟨z, t.2.2, r⟩
          ⟨q.1, ⟨t.1, t.2.1.1, t.2.1.2, q.2.1⟩, q.2.2⟩ := rfl
    erw [hrow]
    have hzero : layerSweep U V 0 i z ⟨i, nilPath i, ⟨u, cu⟩⟩ =
        ⟨z, ⟨u, cu⟩, nilPath z⟩ := by with_unfolding_all rfl
    rw [hzero]
    change (let q := rowFirst c 0 z j ⟨z, nilPath z, r⟩;
      (⟨q.1, ⟨z, u, cu, q.2.1⟩, q.2.2⟩ :
        Σ y : Fin m, FactorPath (forwardFactors (.cons U V rfl rfl c)) i y × Word C 0 y j)) = _
    rw [ih]

set_option maxHeartbeats 1600000 in
-- The dependent sigma transport traverses the complete chain proof.
private theorem rowFirst_succ [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (l : ℕ) (i : Fin n) (j : Fin m)
    (p : Σ x : Fin n, Word A (l + 1) i x × FactorPath (forwardFactors c) x j) :
    let w := p.2.1
    let a : At A i w.1 := ⟨w.2.1, w.2.2.1⟩
    let t := rowFirst c l w.1 j ⟨p.1, w.2.2.2, p.2.2⟩
    let q := phiR c i t.1 ⟨w.1, a, t.2.1⟩
    rowFirst c (l + 1) i j p =
      ⟨q.1, q.2.1, ⟨t.1, q.2.2.1, q.2.2.2, t.2.2⟩⟩ := by
  induction c with
  | @nil n A =>
    rcases p with ⟨x, ⟨v, a, ca, w⟩, ⟨⟨y, hyx, hyj⟩⟩⟩
    subst y
    subst x
    rfl
  | @cons n k m L A B C U V hA hB c ih =>
    subst A
    subst B
    rcases p with ⟨x, ⟨v, a, ca, w⟩, ⟨z, u, cu, r⟩⟩
    let t := layerSweep U V l v z ⟨x, w, ⟨u, cu⟩⟩
    let q := localSweep U V i t.1 ⟨v, ⟨a, ca⟩, t.2.1⟩
    have hrec := ih q.1 j ⟨z, ⟨t.1, q.2.2.1, q.2.2.2, t.2.2⟩, r⟩
    with_unfolding_all exact congrArg (fun e : Σ y : Fin m,
        FactorPath (forwardFactors c) q.1 y × Word C (l + 1) y j =>
      (⟨e.1, ⟨q.1, q.2.1.1, q.2.1.2, e.2.1⟩, e.2.2⟩ :
        Σ y : Fin m, FactorPath (forwardFactors (.cons U V rfl rfl c)) i y ×
          Word C (l + 1) y j)) hrec

/-- The complete row evaluation is the same right-to-left column evaluation. -/
theorem rowFirst_eq_phiRPower [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (l : ℕ) (i : Fin n) (j : Fin m)
    (p : Σ x : Fin n, Word A l i x × FactorPath (forwardFactors c) x j) :
    rowFirst c l i j p = phiRPower c l i j p := by
  induction l generalizing i with
  | zero =>
    rcases p with ⟨x, ⟨⟨v, hvi, hvx⟩⟩, r⟩
    subst v
    subst x
    erw [rowFirst_zero]
    rfl
  | succ l ih =>
    rw [rowFirst_succ]
    dsimp only [phiRPower, pathHeadEquiv, Equiv.trans_apply,
      Equiv.sigmaCongrRight_apply, Equiv.prodCongr_apply]
    rw [ih]
    rfl

/-- Convert the complete actual word to its literal numbered row. -/
def wordToRow {n : ℕ} (A : GroupMat H n n) :
    (l : ℕ) → (i j : Fin n) → (w : Word A l i j) →
      {r : NumberedRow A l // r.vertex 0 = i ∧ r.vertex (Fin.last l) = j ∧
        HEq (rowWord A l r) w}
  | 0, i, j, w => by
    rcases w with ⟨⟨v, hvi, hvj⟩⟩
    subst v
    subst j
    exact ⟨⟨fun _ => i, fun k => Fin.elim0 k⟩, rfl, rfl, HEq.rfl⟩
  | l + 1, i, j, w => by
    rcases w with ⟨k, g, num, w⟩
    obtain ⟨r, hfirst, hlast, hword⟩ := wordToRow A l k j w
    subst k
    subst j
    let r' : NumberedRow A (l + 1) := {
      vertex := Fin.cases i r.vertex
      edge := Fin.cases (⟨g, num⟩ : At A i (r.vertex 0)) r.edge }
    refine ⟨r', rfl, rfl, ?_⟩
    change HEq (⟨r.vertex 0, g, num, rowWord A l r⟩ : Word A (l + 1) i _) _
    rw [eq_of_heq hword]

/-- The actual U factor path as the prescribed right-side vertices and edges. -/
structure RightBoundary {L : ℕ} (data : IndexedChain H L)
    (i : Fin (data.d 0)) (j : Fin (data.d (Fin.last L))) where
  vertex : (k : Fin (L + 1)) → Fin (data.d k)
  edge : (k : Fin L) → At (data.U k) (vertex k.castSucc) (vertex k.succ)
  first : vertex 0 = i
  last : vertex (Fin.last L) = j

/-- Unpack every original factor edge without changing its label or number. -/
def pathToRightBoundary : {L : ℕ} → (data : IndexedChain H L) →
    (i : Fin (data.d 0)) → (j : Fin (data.d (Fin.last L))) →
    FactorPath (forwardFactors (toChain data)) i j → RightBoundary data i j
  | 0, data, i, j, p => by
    rcases p with ⟨⟨v, hvi, hvj⟩⟩
    subst v
    subst j
    exact { vertex := Fin.cases i (fun k => Fin.elim0 k)
            edge := fun k => Fin.elim0 k
            first := rfl
            last := rfl }
  | L + 1, data, i, j, p => by
    rcases p with ⟨k, g, num, p⟩
    obtain ⟨v, e, hfirst, hlast⟩ := pathToRightBoundary (tail data) k j p
    subst k
    exact {
      vertex := Fin.cases i v
      edge := Fin.cases (⟨g, num⟩ : At (data.U 0) i (v 0)) e
      first := rfl
      last := by change v (Fin.last L) = j; exact hlast }

/-- The original typed word and complete R factor path generate the same G34 array. -/
noncomputable def wordFactorArray [LinearOrder H] {L : ℕ} (data : IndexedChain H L)
    (l : ℕ) (i : Fin (data.d 0)) (j : Fin (data.d (Fin.last L)))
    (p : Σ x : Fin (data.d 0), Word (data.A 0) l i x ×
      FactorPath (forwardFactors (toChain data)) x j) : G34Array data l :=
  let r := wordToRow (data.A 0) l i p.1 p.2.1
  let b := pathToRightBoundary data p.1 j p.2.2
  (generateG34 data l b.vertex b.edge r.val (r.property.2.1.trans b.first.symm)).val

/-- The entire actual prescribed U boundary at the last column. -/
def arrayRightPath [LinearOrder H] : {L l : ℕ} → {data : IndexedChain H L} →
    (g : G34Array data l) → FactorPath (forwardFactors (toChain data))
      ((g.row 0).vertex (Fin.last l)) ((g.row (Fin.last L)).vertex (Fin.last l))
  | 0, _l, _data, g => nilPath ((g.row 0).vertex (Fin.last _l))
  | L + 1, l, _data, g => by
    have u : At _ ((g.row 0).vertex (Fin.last l)) ((g.row 1).vertex (Fin.last l)) :=
      congrArg (fun r : NumberedRow (_data.A 1) l => r.vertex (Fin.last l)) (g.nextRow 0) ▸ (g.step 0).u (Fin.last l)
    exact ⟨(g.row 1).vertex (Fin.last l), u.1, u.2, arrayRightPath (arrayTail g)⟩

private theorem rowFirst_step [LinearOrder H] {n k m L l : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) {C : GroupMat H m m}
    (c : Chain H B C L) (r : NumberedRow A l)
    (p : G34Step A B U V hA hB r) (s : NumberedRow B l) (hs : p.next = s)
    (j : Fin m) (rest : FactorPath (forwardFactors c) (s.vertex (Fin.last l)) j) :
    let ulast : At U (r.vertex (Fin.last l)) (s.vertex (Fin.last l)) := congrArg (fun r => r.vertex (Fin.last l)) hs ▸ p.u (Fin.last l)
    let ufirst : At U (r.vertex 0) (s.vertex 0) := congrArg (fun r => r.vertex 0) hs ▸ p.u 0
    rowFirst (.cons U V hA hB c) l (r.vertex 0) j
      ⟨r.vertex (Fin.last l), rowWord A l r,
        ⟨s.vertex (Fin.last l), ulast.1, ulast.2, rest⟩⟩ =
      let q := rowFirst c l (s.vertex 0) j ⟨s.vertex (Fin.last l), rowWord B l s, rest⟩
      ⟨q.1, ⟨s.vertex 0, ufirst.1, ufirst.2, q.2.1⟩, q.2.2⟩ := by
  subst s
  subst A
  subst B
  have hrow : rowFirst (.cons U V rfl rfl c) l (r.vertex 0) j
        ⟨r.vertex (Fin.last l), rowWord (U * V) l r,
          ⟨p.next.vertex (Fin.last l), (p.u (Fin.last l)).1, (p.u (Fin.last l)).2, rest⟩⟩ =
      let t := layerSweep U V l (r.vertex 0) (p.next.vertex (Fin.last l))
        ⟨r.vertex (Fin.last l), rowWord (U * V) l r, p.u (Fin.last l)⟩
      let q := rowFirst c l t.1 j ⟨p.next.vertex (Fin.last l), t.2.2, rest⟩
      ⟨q.1, ⟨t.1, t.2.1.1, t.2.1.2, q.2.1⟩, q.2.2⟩ := rfl
  dsimp only
  erw [hrow]
  erw [g34_layerSweep U V r p]

/-- The complete row-first algorithm evaluates this same entire prescribed array. -/
theorem g34_rowFirst [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (g : G34Array data l) :
    rowFirst (toChain data) l ((g.row 0).vertex 0)
      ((g.row (Fin.last L)).vertex (Fin.last l))
      ⟨(g.row 0).vertex (Fin.last l), rowWord _ l (g.row 0), arrayRightPath g⟩ =
        arrayOutput g := by
  induction L with
  | zero =>
    change rowFirst (.nil (data.A 0)) l ((g.row 0).vertex 0)
      ((g.row 0).vertex (Fin.last l))
      ⟨(g.row 0).vertex (Fin.last l), rowWord _ l (g.row 0),
        nilPath ((g.row 0).vertex (Fin.last l))⟩ = _
    rfl
  | succ L ih =>
    change rowFirst (.cons (data.U 0) (data.V 0) (data.leftFactor 0) (data.rightFactor 0)
      (toChain (tail data))) l _ _ _ = _
    unfold arrayRightPath
    erw [rowFirst_step (data.A 0) (data.A 1) (data.U 0) (data.V 0)
      (data.leftFactor 0) (data.rightFactor 0) (toChain (tail data))
      (g.row 0) (g.step 0) (g.row 1) (g.nextRow 0)]
    erw [ih (arrayTail g)]
    rfl

/-- Column-first evaluation returns the very same left path and bottom word. -/
theorem g34_phiRPower [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (g : G34Array data l) :
    phiRPower (toChain data) l ((g.row 0).vertex 0)
      ((g.row (Fin.last L)).vertex (Fin.last l))
      ⟨(g.row 0).vertex (Fin.last l), rowWord _ l (g.row 0), arrayRightPath g⟩ =
        arrayOutput g := by
  rw [← rowFirst_eq_phiRPower]
  exact g34_rowFirst g

private theorem rowWord_congr {n l : ℕ} {A : GroupMat H n n}
    {r s : NumberedRow A l} (h : r = s) : HEq (rowWord A l r) (rowWord A l s) := by
  cases h
  rfl

/-- The generated array contains the full original top word. -/
theorem wordFactorArray_top [LinearOrder H] {L : ℕ} (data : IndexedChain H L)
    (l : ℕ) (i : Fin (data.d 0)) (j : Fin (data.d (Fin.last L)))
    (p : Σ x : Fin (data.d 0), Word (data.A 0) l i x ×
      FactorPath (forwardFactors (toChain data)) x j) :
    HEq (rowWord (data.A 0) l ((wordFactorArray data l i j p).row 0)) p.2.1 := by
  let r := wordToRow (data.A 0) l i p.1 p.2.1
  let b := pathToRightBoundary data p.1 j p.2.2
  exact (rowWord_congr (generateG34 data l b.vertex b.edge r.val
    (r.property.2.1.trans b.first.symm)).property.1).trans r.property.2.2

private theorem psi0_step [LinearOrder H] {n k m L : ℕ}
    (A : GroupMat H n n) (B : GroupMat H k k)
    (U : GroupMat H n k) (V : GroupMat H k n)
    (hA : A = U * V) (hB : B = V * U) {C : GroupMat H m m}
    (c : Chain H B C L) (r : NumberedRow A (L + 1))
    (p : G34Step A B U V hA hB r) (s : NumberedRow B (L + 1)) (hs : p.next = s) :
    let u : At U (r.vertex 0) (s.vertex 0) := congrArg (fun r => r.vertex 0) hs ▸ p.u 0
    let v : At V (s.vertex (Fin.last L).castSucc) (r.vertex (Fin.last (L + 1))) :=
      congrArg (fun r => r.vertex (Fin.last L).castSucc) hs ▸ p.v (Fin.last L)
    (psi0 (.cons U V hA hB c) (r.vertex 0) (r.vertex (Fin.last (L + 1)))).symm
      (rowWord A (L + 1) r) =
      let q := (psi0 c (s.vertex 0) (s.vertex (Fin.last L).castSucc)).symm
        (rowWord B L (rowPrefix s))
      ⟨q.1, ⟨s.vertex 0, u.1, u.2, q.2.1⟩,
        (pathSnocEquiv (backwardFactors c) V q.1 (r.vertex (Fin.last (L + 1)))).symm
          ⟨s.vertex (Fin.last L).castSucc, q.2.2, v⟩⟩ := by
  subst s
  subst A
  subst B
  dsimp only
  have hcompute {n k m L : ℕ}
      (U : GroupMat H n k) (V : GroupMat H k n) {C : GroupMat H m m}
      (c : Chain H (V * U) C L) (i j : Fin n) (w : Word (U * V) (L + 1) i j) :
      (psi0 (.cons U V rfl rfl c) i j).symm w =
        let p := peelRow U V L i j w
        let q := (psi0 c p.1 p.2.1).symm p.2.2.2.1
        ⟨q.1, ⟨p.1, p.2.2.1.1, p.2.2.1.2, q.2.1⟩,
          (pathSnocEquiv (backwardFactors c) V q.1 j).symm
            ⟨p.2.1, q.2.2, p.2.2.2.2⟩⟩ := rfl
  erw [hcompute, g34_peelRow U V r p]

private theorem arrayLeftPath_prefix [LinearOrder H] {L l : ℕ} {data : IndexedChain H L}
    (g : G34Array data (l + 1)) : arrayLeftPath (arrayPrefix g) = arrayLeftPath g := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (⟨_, _, _, arrayLeftPath (arrayPrefix (arrayTail g))⟩ :
      FactorPath (forwardFactors (toChain data)) _ _) = _
    rw [ih]
    rfl

/-- Literal top triangle boundaries of the same entire G34 square. -/
theorem g34_psi0 [LinearOrder H] {L : ℕ} {data : IndexedChain H L}
    (g : G34Array data L) :
    (psi0 (toChain data) ((g.row 0).vertex 0) ((g.row 0).vertex (Fin.last L))).symm
      (rowWord _ L (g.row 0)) =
      ⟨(g.row (Fin.last L)).vertex 0, arrayLeftPath g, arrayMiddlePath g⟩ := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (psi0 (.cons (data.U 0) (data.V 0) (data.leftFactor 0) (data.rightFactor 0)
      (toChain (tail data))) _ _).symm _ = _
    erw [psi0_step (data.A 0) (data.A 1) (data.U 0) (data.V 0)
      (data.leftFactor 0) (data.rightFactor 0) (toChain (tail data))
      (g.row 0) (g.step 0) (g.row 1) (g.nextRow 0)]
    erw [ih (arrayPrefix (arrayTail g))]
    rw [arrayLeftPath_prefix]
    rfl

theorem reverseChain_snoc {n k m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H k k} {C : GroupMat H m m} (c : Chain H A B L)
    (U : GroupMat H k m) (V : GroupMat H m k) (hB : B = U * V) (hC : C = V * U) :
    reverseChain (chainSnoc c U V hB hC) = .cons V U hC hB (reverseChain c) := by
  induction c with
  | nil A => rfl
  | cons N M hA hD c ih =>
    simp only [chainSnoc, reverseChain, ih]

/-- Inverse triangle at explicitly equal original factor types. -/
private noncomputable def triangleInvAt [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (g : Factors H m n L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g) (i j : Fin n) :
    Word A L i j ≃ Σ v : Fin m, FactorPath f i v × FactorPath g v j :=
  (psi0 c i j).symm.trans (Equiv.cast (by rw [ChainBoundary, hf, hg]))

private theorem triangleInvAt_cons [LinearOrder H] {n k m L : ℕ}
    (U : GroupMat H n k) (V : GroupMat H k n) {C : GroupMat H m m}
    (c : Chain H (V * U) C L) (f : Factors H k m L) (g : Factors H m k L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g)
    (i j : Fin n) (w : Word (U * V) (L + 1) i j) :
    triangleInvAt (.cons U V rfl rfl c) (.cons U f) (factorSnoc g V)
      (by simp only [forwardFactors, hf]) (by simp only [backwardFactors, hg]) i j w =
      let p := peelRow U V L i j w
      let q := triangleInvAt c f g hf hg p.1 p.2.1 p.2.2.2.1
      ⟨q.1, ⟨p.1, p.2.2.1.1, p.2.2.1.2, q.2.1⟩,
        (pathSnocEquiv g V q.1 j).symm ⟨p.2.1, q.2.2, p.2.2.2.2⟩⟩ := by
  cases hf
  cases hg
  rfl

private theorem cast_symm_heq {α β : Type u} (h : α = β) (x : β) :
    HEq ((Equiv.cast h).symm x) x := by
  cases h
  rfl

private theorem triangleInvAt_heq [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (g : Factors H m n L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g)
    (i j : Fin n) (w : Word A L i j) :
    HEq (triangleInvAt c f g hf hg i j w) ((psi0 c i j).symm w) := by
  cases hf
  cases hg
  rfl

private theorem psiL_inv_heq [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i j : Fin m) (w : Word B L i j) :
    HEq ((psiL c i j).symm w) ((psi0 (reverseChain c) i j).symm w) :=
  cast_symm_heq (by simp only [ChainBoundary, reverse_forward, reverse_backward]) _

private theorem psi0_inv_chain_heq [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} {c d : Chain H A B L}
    (h : c = d) (i j : Fin n) (w : Word A L i j) :
    HEq ((psi0 c i j).symm w) ((psi0 d i j).symm w) := by
  cases h
  rfl

private theorem psiL_snoc_inv [LinearOrder H] {n k m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H k k} {C : GroupMat H m m}
    (c : Chain H A B L) (U : GroupMat H k m) (V : GroupMat H m k)
    (hB : B = U * V) (hC : C = V * U)
    (i j : Fin m) (w : Word C (L + 1) i j) :
    let w' : Word (V * U) (L + 1) i j := hC ▸ w
    let p := peelRow V U L i j w'
    let q := (psiL c p.1 p.2.1).symm (hB.symm ▸ p.2.2.2.1)
    HEq ((psiL (chainSnoc c U V hB hC) i j).symm w)
      (⟨q.1, ⟨p.1, p.2.2.1.1, p.2.2.1.2, q.2.1⟩,
        (pathSnocEquiv (forwardFactors c) U q.1 j).symm ⟨p.2.1, q.2.2, p.2.2.2.2⟩⟩ :
        Σ v : Fin n, FactorPath (.cons V (backwardFactors c)) i v ×
          FactorPath (factorSnoc (forwardFactors c) U) v j) := by
  subst B
  subst C
  dsimp only
  have hraw := (psiL_inv_heq (chainSnoc c U V rfl rfl) i j w).trans
    (psi0_inv_chain_heq (reverseChain_snoc c U V rfl rfl) i j w)
  have hnormal := triangleInvAt_heq (.cons V U rfl rfl (reverseChain c))
    (.cons V (backwardFactors c)) (factorSnoc (forwardFactors c) U)
    (by simp only [forwardFactors, reverse_forward])
    (by simp only [backwardFactors, reverse_backward]) i j w
  have h := triangleInvAt_cons V U (reverseChain c) (backwardFactors c)
    (forwardFactors c) (reverse_forward c) (reverse_backward c) i j w
  exact (hraw.trans hnormal.symm).trans (heq_of_eq h)

private def chainInit {L : ℕ} (data : IndexedChain H (L + 1)) : IndexedChain H L where
  d i := data.d i.castSucc
  A i := data.A i.castSucc
  U i := data.U i.castSucc
  V i := data.V i.castSucc
  leftFactor i := data.leftFactor i.castSucc
  rightFactor i := data.rightFactor i.castSucc

private theorem toChain_init {L : ℕ} (data : IndexedChain H (L + 1)) :
    toChain data = chainSnoc (toChain (chainInit data))
      (data.U (Fin.last L)) (data.V (Fin.last L))
      (data.leftFactor (Fin.last L)) (data.rightFactor (Fin.last L)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change Chain.cons (data.U 0) (data.V 0) (data.leftFactor 0) (data.rightFactor 0)
      (toChain (tail data)) = Chain.cons _ _ _ _ _
    rw [ih (tail data)]
    rfl

private def arrayInitTail [LinearOrder H] {L l : ℕ} {data : IndexedChain H (L + 1)}
    (g : G34Array data (l + 1)) : G34Array (chainInit data) l where
  row j := rowTail (g.row j.castSucc)
  step j := stepTail (g.step j.castSucc)
  nextRow j := congrArg rowTail (g.nextRow j.castSucc)

private theorem psiL_step [LinearOrder H] {n k m L : ℕ}
    {A : GroupMat H n n} (B : GroupMat H k k) (C : GroupMat H m m)
    (c : Chain H A B L) (U : GroupMat H k m) (V : GroupMat H m k)
    (hB : B = U * V) (hC : C = V * U) (r : NumberedRow B (L + 1))
    (p : G34Step B C U V hB hC r) (s : NumberedRow C (L + 1)) (hs : p.next = s) :
    let v : At V (s.vertex 0) (r.vertex 1) :=
      congrArg (fun r => r.vertex 0) hs ▸ p.v 0
    let u : At U (r.vertex (Fin.last (L + 1))) (s.vertex (Fin.last (L + 1))) :=
      congrArg (fun r => r.vertex (Fin.last (L + 1))) hs ▸ p.u (Fin.last (L + 1))
    let q := (psiL c (r.vertex 1) (r.vertex (Fin.last (L + 1)))).symm
      (rowWord B L (rowTail r))
    HEq ((psiL (chainSnoc c U V hB hC) (s.vertex 0)
      (s.vertex (Fin.last (L + 1)))).symm (rowWord C (L + 1) s))
      (⟨q.1, ⟨r.vertex 1, v.1, v.2, q.2.1⟩,
        (pathSnocEquiv (forwardFactors c) U q.1 (s.vertex (Fin.last (L + 1)))).symm
          ⟨r.vertex (Fin.last (L + 1)), q.2.2, u⟩⟩ :
        Σ x : Fin n, FactorPath (.cons V (backwardFactors c)) (s.vertex 0) x ×
          FactorPath (factorSnoc (forwardFactors c) U) x
            (s.vertex (Fin.last (L + 1)))) := by
  subst s
  subst B
  subst C
  dsimp only
  have h := psiL_snoc_inv c U V rfl rfl (p.next.vertex 0)
    (p.next.vertex (Fin.last (L + 1))) (rowWord (V * U) (L + 1) p.next)
  dsimp only at h
  erw [g34_reversePeelRow U V r p] at h
  exact h

private theorem pathCons_heq {n k m L : ℕ} (U : GroupMat H n k)
    {f g : Factors H k m L} (h : f = g) (i : Fin n) (x : Fin k) (j : Fin m)
    (u : At U i x) (p : FactorPath f x j) (q : FactorPath g x j) (hp : HEq p q) :
    HEq (⟨x, u.1, u.2, p⟩ : FactorPath (.cons U f) i j)
      (⟨x, u.1, u.2, q⟩ : FactorPath (.cons U g) i j) := by
  cases h
  cases hp
  rfl

private theorem pathSnoc_heq {n k m L : ℕ} {f g : Factors H n k L}
    (h : f = g) (V : GroupMat H k m) (i : Fin n) (x : Fin k) (j : Fin m)
    (p : FactorPath f i x) (q : FactorPath g i x) (hp : HEq p q) (v : At V x j) :
    HEq ((pathSnocEquiv f V i j).symm ⟨x, p, v⟩)
      ((pathSnocEquiv g V i j).symm ⟨x, q, v⟩) := by
  cases h
  cases hp
  rfl

private theorem arrayRightPath_init [LinearOrder H] {L l : ℕ}
    {data : IndexedChain H (L + 1)} (g : G34Array data (l + 1)) :
    let u : At (data.U (Fin.last L)) ((g.row (Fin.last L).castSucc).vertex (Fin.last (l + 1)))
        ((g.row (Fin.last (L + 1))).vertex (Fin.last (l + 1))) :=
      congrArg (fun r => r.vertex (Fin.last (l + 1))) (g.nextRow (Fin.last L)) ▸
        (g.step (Fin.last L)).u (Fin.last (l + 1))
    HEq (arrayRightPath g)
      ((pathSnocEquiv (forwardFactors (toChain (chainInit data))) (data.U (Fin.last L))
        ((g.row 0).vertex (Fin.last (l + 1)))
        ((g.row (Fin.last (L + 1))).vertex (Fin.last (l + 1)))).symm
        ⟨(g.row (Fin.last L).castSucc).vertex (Fin.last (l + 1)),
          arrayRightPath (arrayInitTail g), u⟩) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    dsimp only
    have ht := ih (arrayTail g)
    have hf : forwardFactors (toChain (tail data)) =
        factorSnoc (forwardFactors (toChain (chainInit (tail data))))
          ((tail data).U (Fin.last L)) := by
      rw [toChain_init, forward_snoc]
    exact pathCons_heq (data.U 0) hf _ _ _
      (congrArg (fun r : NumberedRow (data.A 1) (l + 1) =>
        r.vertex (Fin.last (l + 1))) (g.nextRow 0) ▸ (g.step 0).u (Fin.last (l + 1)))
      _ _ ht

private theorem arrayMiddlePath_init [LinearOrder H] {L : ℕ}
    {data : IndexedChain H (L + 1)} (g : G34Array data (L + 1)) :
    let v : At (data.V (Fin.last L)) ((g.row (Fin.last (L + 1))).vertex 0)
        ((g.row (Fin.last L).castSucc).vertex 1) :=
      congrArg (fun r => r.vertex 0) (g.nextRow (Fin.last L)) ▸
        (g.step (Fin.last L)).v 0
    HEq (arrayMiddlePath g)
      (⟨(g.row (Fin.last L).castSucc).vertex 1, v.1, v.2,
        arrayMiddlePath (arrayInitTail g)⟩ :
        FactorPath (.cons (data.V (Fin.last L))
          (backwardFactors (toChain (chainInit data))))
          ((g.row (Fin.last (L + 1))).vertex 0) ((g.row 0).vertex (Fin.last (L + 1)))) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    dsimp only
    have ht := ih (arrayPrefix (arrayTail g))
    have hf : backwardFactors (toChain (tail data)) =
        .cons ((tail data).V (Fin.last L))
          (backwardFactors (toChain (chainInit (tail data)))) := by
      rw [toChain_init, backward_snoc]
    exact pathSnoc_heq hf (data.V 0) _ _ _ _ _ ht
      (congrArg (fun r : NumberedRow (data.A 1) (L + 2) =>
        r.vertex (Fin.last (L + 1)).castSucc) (g.nextRow 0) ▸
          (g.step 0).v (Fin.last (L + 1)))

private theorem psiL_inv_chain_heq [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} {c d : Chain H A B L}
    (h : c = d) (i j : Fin m) (w : Word B L i j) :
    HEq ((psiL c i j).symm w) ((psiL d i j).symm w) := by
  cases h
  rfl

private theorem boundary_heq {n m L : ℕ} {f f' : Factors H m n L}
    {g g' : Factors H n m L} (hf : f = f') (hg : g = g')
    (i j : Fin m) (x : Fin n) (p : FactorPath f i x) (p' : FactorPath f' i x)
    (q : FactorPath g x j) (q' : FactorPath g' x j) (hp : HEq p p') (hq : HEq q q') :
    HEq (⟨x, p, q⟩ : Σ v : Fin n, FactorPath f i v × FactorPath g v j)
      (⟨x, p', q'⟩ : Σ v : Fin n, FactorPath f' i v × FactorPath g' v j) := by
  cases hf
  cases hg
  cases hp
  cases hq
  rfl

/-- The literal bottom triangle recovers the same diagonal S and prescribed right R. -/
theorem g34_psiL [LinearOrder H] {L : ℕ} {data : IndexedChain H L}
    (g : G34Array data L) :
    (psiL (toChain data) ((g.row (Fin.last L)).vertex 0)
      ((g.row (Fin.last L)).vertex (Fin.last L))).symm
      (rowWord _ L (g.row (Fin.last L))) =
      ⟨(g.row 0).vertex (Fin.last L), arrayMiddlePath g, arrayRightPath g⟩ := by
  induction L with
  | zero => rfl
  | succ L ih =>
    have hraw := psiL_inv_chain_heq (toChain_init data)
      ((g.row (Fin.last (L + 1))).vertex 0)
      ((g.row (Fin.last (L + 1))).vertex (Fin.last (L + 1)))
      (rowWord _ (L + 1) (g.row (Fin.last (L + 1))))
    have h := psiL_step (data.A (Fin.last L).castSucc)
      (data.A (Fin.last (L + 1))) (toChain (chainInit data))
      (data.U (Fin.last L)) (data.V (Fin.last L))
      (data.leftFactor (Fin.last L)) (data.rightFactor (Fin.last L))
      (g.row (Fin.last L).castSucc) (g.step (Fin.last L))
      (g.row (Fin.last (L + 1))) (g.nextRow (Fin.last L))
    dsimp only at h
    erw [ih (arrayInitTail g)] at h
    have hf : backwardFactors (toChain data) =
        .cons (data.V (Fin.last L)) (backwardFactors (toChain (chainInit data))) := by
      rw [toChain_init, backward_snoc]
    have hg : forwardFactors (toChain data) =
        factorSnoc (forwardFactors (toChain (chainInit data))) (data.U (Fin.last L)) := by
      rw [toChain_init, forward_snoc]
    have hb := boundary_heq hf hg ((g.row (Fin.last (L + 1))).vertex 0)
      ((g.row (Fin.last (L + 1))).vertex (Fin.last (L + 1)))
      ((g.row 0).vertex (Fin.last (L + 1))) _ _ _ _
      (arrayMiddlePath_init g) (arrayRightPath_init g)
    exact eq_of_heq ((hraw.trans h).trans hb.symm)

/-- Both literal triangles and the complete column sweep on this same square. -/
theorem g34_longR [LinearOrder H] {L : ℕ} {data : IndexedChain H L}
    (g : G34Array data L) :
    phiRPower (toChain data) L ((g.row 0).vertex 0)
      ((g.row (Fin.last L)).vertex (Fin.last L))
      ⟨(g.row 0).vertex (Fin.last L),
        psi0 (toChain data) ((g.row 0).vertex 0) ((g.row 0).vertex (Fin.last L))
          ⟨(g.row (Fin.last L)).vertex 0, arrayLeftPath g, arrayMiddlePath g⟩,
        arrayRightPath g⟩ =
      ⟨(g.row (Fin.last L)).vertex 0, arrayLeftPath g,
        psiL (toChain data) ((g.row (Fin.last L)).vertex 0)
          ((g.row (Fin.last L)).vertex (Fin.last L))
          ⟨(g.row 0).vertex (Fin.last L), arrayMiddlePath g, arrayRightPath g⟩⟩ := by
  have ht := congrArg
    (psi0 (toChain data) ((g.row 0).vertex 0) ((g.row 0).vertex (Fin.last L)))
    (g34_psi0 g)
  simp only [Equiv.apply_symm_apply] at ht
  have hb := congrArg
    (psiL (toChain data) ((g.row (Fin.last L)).vertex 0)
      ((g.row (Fin.last L)).vertex (Fin.last L))) (g34_psiL g)
  simp only [Equiv.apply_symm_apply] at hb
  rw [← ht, ← hb]
  exact g34_phiRPower g

end D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
