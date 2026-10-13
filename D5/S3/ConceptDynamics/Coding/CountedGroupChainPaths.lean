/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupChainPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both long compatibility equations hold on every original typed input. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths.TriangleRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths

open CountedGroupOverlap
open RectangularNilpotenceBarrier

universe u
variable {H : Type u} [Group H] [Fintype H]

attribute [local irreducible] layerSweep localSweep peelRow orderedAtEquiv

/-- Assemble the complete prescribed boundary without changing any numbered edge. -/

def rightBoundaryPath : {L : ℕ} → (data : IndexedChain H L) →
    (v : (k : Fin (L + 1)) → Fin (data.d k)) →
    ((k : Fin L) → At (data.U k) (v k.castSucc) (v k.succ)) →
    FactorPath (forwardFactors (toChain data)) (v 0) (v (Fin.last L))
  | 0, _data, v, _e => nilPath (v 0)
  | L + 1, data, v, e =>
    ⟨v 1, (e 0).1, (e 0).2,
      rightBoundaryPath (tail data) (fun k => v k.succ) (fun k => e k.succ)⟩

private theorem pathToRightBoundary_path {L : ℕ} (data : IndexedChain H L)
    (i : Fin (data.d 0)) (j : Fin (data.d (Fin.last L)))
    (p : FactorPath (forwardFactors (toChain data)) i j) :
    HEq (rightBoundaryPath data (pathToRightBoundary data i j p).vertex
      (pathToRightBoundary data i j p).edge) p := by
  induction L with
  | zero =>
    rcases p with ⟨⟨v, hvi, hvj⟩⟩
    subst v
    subst j
    rfl
  | succ L ih =>
    rcases p with ⟨x, h, num, p⟩
    have ht := ih (tail data) x j p
    rcases hb : pathToRightBoundary (tail data) x j p with ⟨v, e, hv, hj⟩
    rw [hb] at ht
    subst x
    dsimp only [pathToRightBoundary, rightBoundaryPath]
    rw [hb]
    dsimp only
    cases hj
    exact heq_of_eq (congrArg (fun p =>
      (⟨v 0, h, num, p⟩ : FactorPath (forwardFactors (toChain data)) i (v (Fin.last L))))
      (eq_of_heq ht))

private theorem factorPath_cons_heq {n k m L : ℕ} (U : GroupMat H n k)
    (f : Factors H k m L) {i i' : Fin n} {x x' : Fin k} {j j' : Fin m}
    (hi : i = i') (hx : x = x') (hj : j = j')
    (u : At U i x) (u' : At U i' x')
    (p : FactorPath f x j) (p' : FactorPath f x' j') (hu : HEq u u') (hp : HEq p p') :
    HEq (⟨x, u.1, u.2, p⟩ : FactorPath (.cons U f) i j)
      (⟨x', u'.1, u'.2, p'⟩ : FactorPath (.cons U f) i' j') := by
  cases hi
  cases hx
  cases hj
  cases hu
  cases hp
  rfl

private theorem nilPath_heq {n : ℕ} {i j : Fin n} (h : i = j) :
    HEq (nilPath (H := H) i) (nilPath (H := H) j) := by
  cases h
  rfl

private theorem arrayRightPath_boundary [LinearOrder H] {L l : ℕ}
    {data : IndexedChain H L} (g : G34Array data l)
    (v : (k : Fin (L + 1)) → Fin (data.d k))
    (e : (k : Fin L) → At (data.U k) (v k.castSucc) (v k.succ))
    (hv : ∀ k, (g.row k).vertex (Fin.last l) = v k)
    (he : ∀ k, HEq ((g.step k).u (Fin.last l)) (e k)) :
    HEq (arrayRightPath g) (rightBoundaryPath data v e) := by
  induction L with
  | zero =>
    exact nilPath_heq (hv 0)
  | succ L ih =>
    have hp := ih (arrayTail g) (fun k => v k.succ) (fun k => e k.succ)
      (fun k => hv k.succ) (fun k => he k.succ)
    have hu := (eqRec_heq (φ := fun x =>
      At (data.U 0) ((g.row 0).vertex (Fin.last l)) x)
      (congrArg (fun r : NumberedRow (data.A 1) l => r.vertex (Fin.last l)) (g.nextRow 0))
        ((g.step 0).u (Fin.last l))).trans (he 0)
    exact factorPath_cons_heq (data.U 0) (forwardFactors (toChain (tail data)))
      (hv 0) (hv 1) (hv (Fin.last (L + 1))) _ _ _ _ hu hp

/-- The generated right boundary is the full original factor path. -/
theorem wordFactorArray_right [LinearOrder H] {L : ℕ} (data : IndexedChain H L)
    (l : ℕ) (i : Fin (data.d 0)) (j : Fin (data.d (Fin.last L)))
    (p : Σ x : Fin (data.d 0), Word (data.A 0) l i x ×
      FactorPath (forwardFactors (toChain data)) x j) :
    HEq (arrayRightPath (wordFactorArray data l i j p)) p.2.2 := by
  let r := wordToRow (data.A 0) l i p.1 p.2.1
  let b := pathToRightBoundary data p.1 j p.2.2
  let g := generateG34 data l b.vertex b.edge r.val (r.property.2.1.trans b.first.symm)
  exact (arrayRightPath_boundary g.val b.vertex b.edge g.property.2.1
    g.property.2.2).trans (pathToRightBoundary_path data p.1 j p.2.2)

private theorem indexedModel {n m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H m m} (c : Chain H A B L) :
    ∃ data : IndexedChain H L, data.d 0 = n ∧ data.d (Fin.last L) = m ∧
      HEq (data.A 0) A ∧ HEq (data.A (Fin.last L)) B ∧ HEq (toChain data) c := by
  induction c with
  | @nil n A =>
    exact ⟨{
      d := fun _ => n
      A := fun _ => A
      U := fun i => Fin.elim0 i
      V := fun i => Fin.elim0 i
      leftFactor := fun i => Fin.elim0 i
      rightFactor := fun i => Fin.elim0 i },
      rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  | @cons n k m L A B C U V hA hB c ih =>
    obtain ⟨data, hn, hm, hfirst, hlast, hc⟩ := ih
    cases hn
    cases hm
    cases hfirst
    cases hlast
    have hc' := eq_of_heq hc
    subst c
    let d : Fin (L + 2) → ℕ := Fin.cases n data.d
    let matrices : (i : Fin (L + 2)) → GroupMat H (d i) (d i) := Fin.cases A data.A
    let us : (i : Fin (L + 1)) → GroupMat H (d i.castSucc) (d i.succ) :=
      Fin.cases U data.U
    let vs : (i : Fin (L + 1)) → GroupMat H (d i.succ) (d i.castSucc) :=
      Fin.cases V data.V
    refine ⟨{
      d := d
      A := matrices
      U := us
      V := vs
      leftFactor := Fin.cases hA data.leftFactor
      rightFactor := Fin.cases hB data.rightFactor }, rfl, rfl, HEq.rfl, HEq.rfl, ?_⟩
    rfl

private theorem wordFactorArray_endpoints [LinearOrder H] {L : ℕ} (data : IndexedChain H L)
    (l : ℕ) (i : Fin (data.d 0)) (j : Fin (data.d (Fin.last L)))
    (p : Σ x : Fin (data.d 0), Word (data.A 0) l i x ×
      FactorPath (forwardFactors (toChain data)) x j) :
    ((wordFactorArray data l i j p).row 0).vertex 0 = i ∧
    ((wordFactorArray data l i j p).row 0).vertex (Fin.last l) = p.1 ∧
    ((wordFactorArray data l i j p).row (Fin.last L)).vertex (Fin.last l) = j := by
  let r := wordToRow (data.A 0) l i p.1 p.2.1
  let b := pathToRightBoundary data p.1 j p.2.2
  let g := generateG34 data l b.vertex b.edge r.val (r.property.2.1.trans b.first.symm)
  exact ⟨(congrArg (fun r : NumberedRow (data.A 0) l => r.vertex 0) g.property.1).trans
      r.property.1,
    (congrArg (fun r : NumberedRow (data.A 0) l => r.vertex (Fin.last l))
      g.property.1).trans r.property.2.1,
    (g.property.2.1 (Fin.last L)).trans b.last⟩

/-- The original long R law holds at every complete typed input of the supplied chain. -/
theorem phiRPower_long [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i x : Fin n) (y j : Fin m)
    (r : FactorPath (forwardFactors c) i y) (s : FactorPath (backwardFactors c) y x)
    (r' : FactorPath (forwardFactors c) x j) :
    phiRPower c L i j ⟨x, psi0 c i x ⟨y, r, s⟩, r'⟩ =
      ⟨y, r, psiL c y j ⟨x, s, r'⟩⟩ := by
  obtain ⟨data, hn, hm, hfirst, hlast, hc⟩ := indexedModel c
  cases hn
  cases hm
  cases hfirst
  cases hlast
  have hc' := eq_of_heq hc
  subst c
  let p : Σ x : Fin (data.d 0), Word (data.A 0) L i x ×
      FactorPath (forwardFactors (toChain data)) x j :=
    ⟨x, psi0 (toChain data) i x ⟨y, r, s⟩, r'⟩
  have hend := wordFactorArray_endpoints data L i j p
  have htop := wordFactorArray_top data L i j p
  have hright := wordFactorArray_right data L i j p
  generalize hg : wordFactorArray data L i j p = g at hend htop hright
  dsimp only [p] at hend htop hright
  rcases hend with ⟨hi, hx, hj⟩
  cases hi
  cases hx
  cases hj
  have ht := g34_psi0 g
  rw [eq_of_heq htop, Equiv.symm_apply_apply] at ht
  obtain ⟨hy, hrs⟩ := Sigma.mk.inj ht
  cases hy
  have hr := congrArg Prod.fst (eq_of_heq hrs)
  have hs := congrArg Prod.snd (eq_of_heq hrs)
  dsimp only at hr hs
  rw [hr, hs, ← eq_of_heq hright]
  exact g34_longR g

private theorem reverseChain_reverse {n m L : ℕ} {A : GroupMat H n n}
    {B : GroupMat H m m} (c : Chain H A B L) : reverseChain (reverseChain c) = c := by
  induction c with
  | nil A => rfl
  | cons U V hA hB c ih =>
    simp only [reverseChain, reverseChain_snoc, ih]

private noncomputable def triangleAt [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (g : Factors H m n L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g) (i j : Fin n) :
    (Σ x : Fin m, FactorPath f i x × FactorPath g x j) ≃ Word A L i j :=
  (Equiv.cast (by rw [ChainBoundary, hf, hg])).trans (psi0 c i j)

private noncomputable def terminalAt [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (g : Factors H m n L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g) (i j : Fin m) :
    (Σ x : Fin n, FactorPath g i x × FactorPath f x j) ≃ Word B L i j :=
  (Equiv.cast (by rw [hf, hg])).trans (psiL c i j)

private noncomputable def sweepAt [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (hf : forwardFactors c = f) (l : ℕ)
    (i : Fin n) (j : Fin m) :
    (Σ x : Fin n, Word A l i x × FactorPath f x j) ≃
      Σ y : Fin m, FactorPath f i y × Word B l y j :=
  (Equiv.cast (by rw [hf])).trans
    ((phiRPower c l i j).trans (Equiv.cast (by rw [hf])))

private theorem longAt [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (f : Factors H n m L) (g : Factors H m n L)
    (hf : forwardFactors c = f) (hg : backwardFactors c = g)
    (i x : Fin n) (y j : Fin m)
    (r : FactorPath f i y) (s : FactorPath g y x) (r' : FactorPath f x j) :
    sweepAt c f hf L i j ⟨x, triangleAt c f g hf hg i x ⟨y, r, s⟩, r'⟩ =
      ⟨y, r, terminalAt c f g hf hg y j ⟨x, s, r'⟩⟩ := by
  cases hf
  cases hg
  exact phiRPower_long c i x y j r s r'

private theorem cast_trans_apply_heq {α β γ : Type u} (h : α = β) (k : β = γ) (p : α) :
    HEq (Equiv.cast k (Equiv.cast h p)) p := by
  cases h
  cases k
  rfl

private theorem psi0_apply_chain_heq [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} {c d : Chain H A B L}
    (h : c = d) (i j : Fin n) (p : ChainBoundary c i j) (q : ChainBoundary d i j)
    (hp : HEq p q) : HEq (psi0 c i j p) (psi0 d i j q) := by
  cases h
  cases hp
  rfl

private theorem terminalAt_reverse [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L) (i j : Fin n) :
    terminalAt (reverseChain c) (backwardFactors c) (forwardFactors c)
      (reverse_forward c) (reverse_backward c) i j = psi0 c i j := by
  apply Equiv.ext
  intro p
  dsimp only [terminalAt, psiL, Equiv.trans_apply]
  exact eq_of_heq (psi0_apply_chain_heq (reverseChain_reverse c) i j _ p
    (cast_trans_apply_heq _ _ p))

/-- The original long S law uses the reversed supplied chain at the same R,S tuple. -/
theorem phiSPower_long [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i x : Fin m) (y j : Fin n)
    (s : FactorPath (backwardFactors c) i y) (r : FactorPath (forwardFactors c) y x)
    (s' : FactorPath (backwardFactors c) x j) :
    phiSPower c L i j ⟨x, psiL c i x ⟨y, s, r⟩, s'⟩ =
      ⟨y, s, psi0 c y j ⟨x, r, s'⟩⟩ := by
  have h := longAt (reverseChain c) (backwardFactors c) (forwardFactors c)
    (reverse_forward c) (reverse_backward c) i x y j s r s'
  rw [terminalAt_reverse] at h
  exact h

/-- Conjugate the complete R sweep by the same whole-fiber rank at both boundaries. -/
noncomputable def matrixPhiRPower [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (l : ℕ) (i : Fin n) (j : Fin m) :
    (Σ x : Fin n, Word A l i x × At (R c) x j) ≃
      Σ y : Fin m, At (R c) i y × Word B l y j :=
  (Equiv.sigmaCongrRight fun x => Equiv.prodCongr (Equiv.refl _)
    (pathAtEquiv (forwardFactors c) x j)).trans
      ((phiRPower c l i j).trans (Equiv.sigmaCongrRight fun y =>
        Equiv.prodCongr (pathAtEquiv (forwardFactors c) i y).symm (Equiv.refl _)))

/-- Conjugate the complete S sweep by that same original S rank. -/
noncomputable def matrixPhiSPower [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (l : ℕ) (i : Fin m) (j : Fin n) :
    (Σ x : Fin m, Word B l i x × At (S c) x j) ≃
      Σ y : Fin n, At (S c) i y × Word A l y j :=
  (Equiv.sigmaCongrRight fun x => Equiv.prodCongr (Equiv.refl _)
    (pathAtEquiv (backwardFactors c) x j)).trans
      ((phiSPower c l i j).trans (Equiv.sigmaCongrRight fun y =>
        Equiv.prodCongr (pathAtEquiv (backwardFactors c) i y).symm (Equiv.refl _)))

/-- The long R equation uses one synchronous global rank for every R,S occurrence. -/
theorem matrixPhiRPower_long [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i x : Fin n) (y j : Fin m) (r : At (R c) i y) (s : At (S c) y x)
    (r' : At (R c) x j) :
    matrixPhiRPower c L i j ⟨x, matrixPsi0 c i x ⟨y, r, s⟩, r'⟩ =
      ⟨y, r, matrixPsiL c y j ⟨x, s, r'⟩⟩ := by
  let finish := Equiv.sigmaCongrRight fun y : Fin m =>
    Equiv.prodCongr (pathAtEquiv (forwardFactors c) i y).symm
      (Equiv.refl (Word B L y j))
  have h := congrArg finish (phiRPower_long c i x y j
    (pathAtEquiv (forwardFactors c) i y r)
    (pathAtEquiv (backwardFactors c) y x s)
    (pathAtEquiv (forwardFactors c) x j r'))
  refine h.trans ?_
  change (⟨y, (pathAtEquiv (forwardFactors c) i y).symm
    (pathAtEquiv (forwardFactors c) i y r),
    matrixPsiL c y j ⟨x, s, r'⟩⟩ : Σ y : Fin m, At (R c) i y × Word B L y j) = _
  rw [Equiv.symm_apply_apply]

/-- The long S equation uses exactly the same concrete endpoint matrices and ranks. -/
theorem matrixPhiSPower_long [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L)
    (i x : Fin m) (y j : Fin n) (s : At (S c) i y) (r : At (R c) y x)
    (s' : At (S c) x j) :
    matrixPhiSPower c L i j ⟨x, matrixPsiL c i x ⟨y, s, r⟩, s'⟩ =
      ⟨y, s, matrixPsi0 c y j ⟨x, r, s'⟩⟩ := by
  let finish := Equiv.sigmaCongrRight fun y : Fin n =>
    Equiv.prodCongr (pathAtEquiv (backwardFactors c) i y).symm
      (Equiv.refl (Word A L y j))
  have h := congrArg finish (phiSPower_long c i x y j
    (pathAtEquiv (backwardFactors c) i y s)
    (pathAtEquiv (forwardFactors c) y x r)
    (pathAtEquiv (backwardFactors c) x j s'))
  refine h.trans ?_
  change (⟨y, (pathAtEquiv (backwardFactors c) i y).symm
    (pathAtEquiv (backwardFactors c) i y s),
    matrixPsi0 c y j ⟨x, r, s'⟩⟩ : Σ y : Fin n, At (S c) i y × Word A L y j) = _
  rw [Equiv.symm_apply_apply]

/-- The original same-tuple certificate, with both laws universally quantified. -/
structure Compatibility [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L) : Prop where
  cumulative : A * R c = R c * B ∧ B * S c = S c * A ∧
    R c * S c = A ^ L ∧ S c * R c = B ^ L
  longR : ∀ (i x : Fin n) (y j : Fin m) (r : At (R c) i y)
    (s : At (S c) y x) (r' : At (R c) x j),
    matrixPhiRPower c L i j ⟨x, matrixPsi0 c i x ⟨y, r, s⟩, r'⟩ =
      ⟨y, r, matrixPsiL c y j ⟨x, s, r'⟩⟩
  longS : ∀ (i x : Fin m) (y j : Fin n) (s : At (S c) i y)
    (r : At (R c) y x) (s' : At (S c) x j),
    matrixPhiSPower c L i j ⟨x, matrixPsiL c i x ⟨y, s, r⟩, s'⟩ =
      ⟨y, s, matrixPsi0 c y j ⟨x, r, s'⟩⟩

/-- Both original long laws and all four equations at (A,B,R c,S c,L). -/
theorem original27_2 [LinearOrder H] {n m L : ℕ}
    {A : GroupMat H n n} {B : GroupMat H m m} (c : Chain H A B L) :
    Compatibility c :=
  ⟨cumulative_equations c, matrixPhiRPower_long c, matrixPhiSPower_long c⟩

end D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
