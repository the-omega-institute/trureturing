/- GID: D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/TwistedPeriodicHistories
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Positive twisted periods of actual bilateral expanded histories are reconstructed from finite numbered loop words with the ordered conjugacy seam, yielding finite enumeration and exact coefficient counts. -/

import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Algebra.Group.End

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)

universe u
variable {H : Type u} [Group H] [Fintype H] {n j : ℕ}
local instance : DecidableEq H := Classical.decEq H

/-- Actual bilateral histories satisfying the positive-time twist equation. -/
def TwistedPeriod (C : GroupMat H n n) (h : H) (j : ℕ) :=
  {x : History (expandedGraph C) //
    (shift (expandedGraph C))^[j] x = groupHistory C h x}

/-- A numbered loop word and its actual initial group coordinate. -/
abbrev SeamWords (C : GroupMat H n n) (h : H) (hj : 0 < j) :=
  Σ i : Fin n, Σ z : H, WordFiber C hj i i (z⁻¹ * h * z)

private theorem window_seam (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (x : TwistedPeriod C h j) :
    let w := forgetWord (historyWindow (expandedGraph C) x.val 0 j)
    let z := (x.val.val 0).2
    wordTarget hj w = wordSource hj w ∧ totalLabel w = z⁻¹ * h * z := by
  dsimp only
  let W := historyWindow (expandedGraph C) x.val 0 j
  let w := forgetWord W
  let z := (x.val.val 0).2
  have coords : liftWord w z = W :=
    (expandedWordCoordinates C hj).symm_apply_apply W
  have twisted := congrArg (fun y : History (expandedGraph C) => y.val 0) x.property
  rw [shift_iterate_translate] at twisted
  change x.val.val (0 + (j : ℤ)) = ((x.val.val 0).1, h * (x.val.val 0).2) at twisted
  simp only [zero_add] at twisted
  have seam : (wordTarget hj w, z * totalLabel w) = (wordSource hj w, h * z) := by
    rw [← lift_target hj w z]
    rw [coords]
    change (expandedGraph C).target (x.val.val (0 + ((j - 1 : ℕ) : ℤ))) = _
    have last : (0 : ℤ) + ((j - 1 : ℕ) : ℤ) + 1 = (j : ℤ) := by omega
    rw [x.val.property (0 + ((j - 1 : ℕ) : ℤ)), last, twisted]
    rfl
  refine ⟨congrArg Prod.fst seam, ?_⟩
  have hs := congrArg Prod.snd seam
  change z * totalLabel w = h * z at hs
  calc
    totalLabel w = z⁻¹ * (z * totalLabel w) := by simp
    _ = z⁻¹ * (h * z) := congrArg (fun a => z⁻¹ * a) hs
    _ = z⁻¹ * h * z := (mul_assoc _ _ _).symm

/-- Restriction uses the original expanded-word coordinate equivalence. -/
def restrict (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (x : TwistedPeriod C h j) : SeamWords C h hj :=
  let w := forgetWord (historyWindow (expandedGraph C) x.val 0 j)
  ⟨wordSource hj w, (x.val.val 0).2,
    ⟨w, rfl, (window_seam C h hj x).1, (window_seam C h hj x).2⟩⟩

private def extensionEdge (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) (t : ℤ) : Edge C × H :=
  let a := blockAddress hj t
  (p.2.2.val.edge a.2, h ^ a.1 * (p.2.1 * prefixLabel p.2.2.val a.2.val))

omit [Fintype H] in
private theorem extensionEdge_at (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) (q : ℤ) (r : Fin j) :
    extensionEdge C h hj p (assemble j (q,r)) =
      (liftWord p.2.2.val (h^q * p.2.1)).edge r := by
  simp only [extensionEdge, address_assemble, liftWord, mul_assoc]

private theorem extension_legal (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) (t : ℤ) :
    (expandedGraph C).target (extensionEdge C h hj p t) =
      (expandedGraph C).source (extensionEdge C h hj p (t+1)) := by
  let q := (blockAddress hj t).1
  let r := (blockAddress hj t).2
  have rep : assemble j (q,r) = t := assemble_address hj t
  rw [← rep]
  by_cases hn : r.val + 1 < j
  · let r' : Fin j := ⟨r.val+1, hn⟩
    have next : assemble j (q,r)+1 = assemble j (q,r') := by
      simp only [assemble, r', Int.natCast_add, Int.natCast_one]
      ring
    rw [next, extensionEdge_at, extensionEdge_at]
    exact (liftWord p.2.2.val (h^q * p.2.1)).legal r hn
  · have hr : r = (⟨j-1,by omega⟩ : Fin j) := by apply Fin.ext; dsimp; omega
    let zero : Fin j := ⟨0,hj⟩
    have next : assemble j (q,r)+1 = assemble j (q+1,zero) := by
      simp only [assemble, zero, Int.natCast_zero]
      have hlast : (r.val : ℤ)+1 = j := by omega
      nlinarith
    rw [next, extensionEdge_at, extensionEdge_at, hr, lift_target hj, lift_source hj]
    apply Prod.ext
    · exact p.2.2.property.2.1.trans p.2.2.property.1.symm
    · rw [p.2.2.property.2.2, zpow_add_one]
      simp only [mul_assoc, mul_inv_cancel_left]

/-- Extension is legal at every signed integer address, including block seams. -/
def extension (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) : History (expandedGraph C) :=
  ⟨extensionEdge C h hj p, extension_legal C h hj p⟩

private theorem extension_twist (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) :
    (shift (expandedGraph C))^[j] (extension C h hj p) =
      groupHistory C h (extension C h hj p) := by
  rw [shift_iterate_translate]
  apply Subtype.ext
  funext t
  let q := (blockAddress hj t).1
  let r := (blockAddress hj t).2
  have rep : assemble j (q,r) = t := assemble_address hj t
  have next : assemble j (q,r)+(j:ℤ) = assemble j (q+1,r) := by
    simp only [assemble]
    ring
  change extensionEdge C h hj p (t+(j:ℤ)) =
    ((extensionEdge C h hj p t).1,h*(extensionEdge C h hj p t).2)
  rw [← rep, next, extensionEdge_at, extensionEdge_at]
  apply Prod.ext
  · rfl
  · simp only [liftWord, zpow_add_one, mul_assoc]
    rw [← mul_assoc h (h^q), Commute.self_zpow h q |>.eq]
    simp only [mul_assoc]

/-- The extension retains the actual shift equation, rather than only a count. -/
def extend (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) : TwistedPeriod C h j :=
  ⟨extension C h hj p, extension_twist C h hj p⟩

omit [Fintype H] in
private theorem signed_recovery (C : GroupMat H n n) (h : H)
    (x : TwistedPeriod C h j) (q t : ℤ) :
    x.val.val (t + q * (j : ℤ)) =
      ((x.val.val t).1, h^q * (x.val.val t).2) := by
  let T : Multiplicative ℤ →* Equiv.Perm (History (expandedGraph C)) :=
    { toFun a :=
        { toFun := translate (expandedGraph C) a.toAdd
          invFun := translate (expandedGraph C) (-a.toAdd)
          left_inv := by
            intro y
            apply Subtype.ext
            funext i
            simp [translate]
          right_inv := by
            intro y
            apply Subtype.ext
            funext i
            simp [translate] }
      map_one' := by
        apply Equiv.ext
        intro y
        apply Subtype.ext
        funext i
        simp [translate]
      map_mul' := by
        intro a b
        apply Equiv.ext
        intro y
        apply Subtype.ext
        funext i
        simp [translate, add_comm, add_left_comm] }
  let U : H →* Equiv.Perm (History (expandedGraph C)) :=
    { toFun a :=
        { toFun := groupHistory C a
          invFun := groupHistory C a⁻¹
          left_inv := by
            intro y
            apply Subtype.ext
            funext i
            simp [groupHistory]
          right_inv := by
            intro y
            apply Subtype.ext
            funext i
            simp [groupHistory] }
      map_one' := by
        apply Equiv.ext
        intro y
        apply Subtype.ext
        funext i
        simp [groupHistory]
      map_mul' := by
        intro a b
        apply Equiv.ext
        intro y
        apply Subtype.ext
        funext i
        simp [groupHistory, mul_assoc] }
  have comm : Commute (U h) (T (Multiplicative.ofAdd (j:ℤ))) := by
    apply Equiv.ext
    intro y
    rfl
  have fixed : Function.IsFixedPt
      (⇑((U h)⁻¹ * T (Multiplicative.ofAdd (j:ℤ)))) x.val := by
    change groupHistory C h⁻¹ (translate (expandedGraph C) (j:ℤ) x.val) = x.val
    rw [← shift_iterate_translate, x.property]
    apply Subtype.ext
    funext i
    simp [groupHistory]
  have fq := fixed.perm_zpow q
  rw [comm.inv_left.mul_zpow, inv_zpow] at fq
  have eqpow : (T (Multiplicative.ofAdd (j:ℤ)) ^ q) x.val = (U h ^ q) x.val :=
    (U h ^ q).symm_apply_eq.mp fq
  rw [← T.map_zpow (Multiplicative.ofAdd (j:ℤ)) q, ← U.map_zpow h q] at eqpow
  have coord :=  congrArg (fun y : History (expandedGraph C) => y.val t) eqpow
  simpa [T, U, translate, groupHistory, toAdd_zpow,
    zsmul_eq_mul] using coord

private theorem extension_window (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) :
    historyWindow (expandedGraph C) (extension C h hj p) 0 j =
      liftWord p.2.2.val p.2.1 := by
  apply legalWord_ext
  funext r
  have coord :=  extensionEdge_at C h hj p 0 r
  simpa [historyWindow, extension, assemble] using coord

private theorem extend_restrict (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (x : TwistedPeriod C h j) : extend C h hj (restrict C h hj x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  let q := (blockAddress hj t).1
  let r := (blockAddress hj t).2
  have rep : assemble j (q,r) = t := assemble_address hj t
  change extensionEdge C h hj (restrict C h hj x) t = x.val.val t
  rw [← rep, extensionEdge_at]
  let W := historyWindow (expandedGraph C) x.val 0 j
  have coords := congrArg (fun w : LegalWord (expandedGraph C) j => w.edge r)
    ((expandedWordCoordinates C hj).symm_apply_apply W)
  change (liftWord (forgetWord W) (W.edge ⟨0,hj⟩).2).edge r = W.edge r at coords
  have recovery := signed_recovery C h x q (r.val:ℤ)
  have addr : (r.val:ℤ) + q * (j:ℤ) = assemble j (q,r) := by
    simp only [assemble]
    ring
  rw [addr] at recovery
  rw [recovery]
  simpa only [restrict, liftWord, W, historyWindow, zero_add, Int.natCast_zero, mul_assoc] using
    congrArg (fun e : Edge C × H => (e.1,h^q * e.2)) coords

private theorem restrict_extend (C : GroupMat H n n) (h : H) (hj : 0 < j)
    (p : SeamWords C h hj) : restrict C h hj (extend C h hj p) = p := by
  rcases p with ⟨i,z,w⟩
  have coords := (expandedWordCoordinates C hj).apply_symm_apply (w.val,z)
  have win := extension_window C h hj (⟨i,z,w⟩ : SeamWords C h hj)
  have hw : forgetWord (historyWindow (expandedGraph C)
      (extension C h hj ⟨i,z,w⟩) 0 j) = w.val := by
    rw [win]
    exact congrArg Prod.fst coords
  have hz : ((extension C h hj ⟨i,z,w⟩).val 0).2 = z := by
    have hz' := congrArg (fun W : LegalWord (expandedGraph C) j =>
      (W.edge ⟨0,hj⟩).2) win
    have hc : ((liftWord w.val z).edge ⟨0,hj⟩).2 = z := congrArg Prod.snd coords
    calc
      ((extension C h hj ⟨i,z,w⟩).val 0).2 =
          ((liftWord w.val z).edge ⟨0,hj⟩).2 := by
        simpa only [historyWindow, Fin.val_mk, Int.natCast_zero, add_zero] using hz'
      _ = z := hc
  have ext : ∀ a b : SeamWords C h hj,
      a.2.2.val = b.2.2.val → a.2.1 = b.2.1 → a = b := by
    intro a b hab hzz
    rcases a with ⟨ia,za,wa,hsa,hta,hga⟩
    rcases b with ⟨ib,zb,wb,hsb,htb,hgb⟩
    dsimp only at hab hzz
    subst wb
    subst zb
    subst ia
    subst ib
    rfl
  exact ext (restrict C h hj (extend C h hj ⟨i,z,w⟩)) ⟨i,z,w⟩ hw hz

/-- Actual restriction and total signed extension are mutually inverse. -/
def twistedPeriodEquiv (C : GroupMat H n n) (h : H) (hj : 0 < j) :
    TwistedPeriod C h j ≃ Σ i : Fin n, Σ z : H, WordFiber C hj i i (z⁻¹*h*z) where
  toFun := restrict C h hj
  invFun := extend C h hj
  left_inv := extend_restrict C h hj
  right_inv := restrict_extend C h hj

/-- Finiteness is transported from actual finite numbered words. -/
@[instance_reducible] def twistedPeriodFintype (C : GroupMat H n n) (h : H) (hj : 0 < j) :
    Fintype (TwistedPeriod C h j) :=
  Fintype.ofEquiv (SeamWords C h hj) (twistedPeriodEquiv C h hj).symm

/-- The count of actual histories consumes the reconstruction and the original
finite word counting theorem directly. -/
theorem twistedPeriod_card (C : GroupMat H n n) (h : H) (hj : 0 < j) :
    @Fintype.card (TwistedPeriod C h j) (twistedPeriodFintype C h hj) =
      ∑ i : Fin n, ∑ z : H, ((C^j) i i).coeff (z⁻¹*h*z) := by
  let := twistedPeriodFintype C h hj
  rw [Fintype.card_congr (twistedPeriodEquiv C h hj)]
  simp only [Fintype.card_sigma, wordFiber_card]

end D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
