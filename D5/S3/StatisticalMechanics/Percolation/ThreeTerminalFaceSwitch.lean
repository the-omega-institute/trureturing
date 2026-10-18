/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceSwitch
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceSwitch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed exchange of actual edge coordinates cancels complementary terminal modes on an ac-free face. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalFaceSeparation ThreeTerminalCactusGate
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

/-- The number of open copies of one edge in an ordered pair. -/
def multiplicity (x y : Bool) : ℕ := (if x then 1 else 0)+(if y then 1 else 0)

/-- The face containing a reference ordered pair, defined by actual edge multiplicities. -/
def Face {E : Type*} (r q : (E → Bool) × (E → Bool)) : Prop :=
  ∀ e, multiplicity (q.1 e) (q.2 e) = multiplicity (r.1 e) (r.2 e)

/-- Exchange a fixed set of edge coordinates between the two configurations. -/
noncomputable def swap {E : Type*} (S : Set E)
    (q : (E → Bool) × (E → Bool)) : (E → Bool) × (E → Bool) := by
  classical
  exact (fun e => if e ∈ S then q.2 e else q.1 e,
    fun e => if e ∈ S then q.1 e else q.2 e)

private lemma swap_face {E : Type*} (S : Set E)
    (r q : (E → Bool) × (E → Bool)) (hq : Face r q) : Face r (swap S q) := by
  classical
  intro e
  by_cases he : e ∈ S
  · simpa [swap,he,multiplicity,add_comm] using hq e
  · simpa [swap,he] using hq e

private lemma swap_swap {E : Type*} (S : Set E) (q : (E → Bool) × (E → Bool)) :
    swap S (swap S q) = q := by
  classical
  apply Prod.ext <;> funext e <;> by_cases he : e ∈ S <;> simp [swap,he]

/-- Edges open in both copies are forced open throughout their face. -/
def forced {V E : Type*} (ends : E → V × V) (r : (E → Bool) × (E → Bool)) :
    SimpleGraph V := openGraph ends (fun e => r.1 e && r.2 e)

/-- Every edge open in either reference copy is available throughout the face. -/
def allowed {V E : Type*} (ends : E → V × V) (r : (E → Bool) × (E → Bool)) :
    SimpleGraph V := openGraph ends (fun e => r.1 e || r.2 e)

private lemma openGraph_mono {V E : Type*} (ends : E → V × V)
    {ω η : E → Bool} (h : ∀ e, ω e = true → η e = true) :
    openGraph ends ω ≤ openGraph ends η := by
  intro x y hxy
  rcases hxy with ⟨hne,⟨e,he,hexy⟩ | ⟨e,he,heyx⟩⟩
  · exact ⟨hne,Or.inl ⟨e,h e he,hexy⟩⟩
  · exact ⟨hne,Or.inr ⟨e,h e he,heyx⟩⟩

private lemma face_interval {V E : Type*} (ends : E → V × V)
    (r q : (E → Bool) × (E → Bool)) (hq : Face r q) :
    forced ends r ≤ openGraph ends q.1 ∧ openGraph ends q.1 ≤ allowed ends r := by
  constructor
  · apply openGraph_mono
    intro e he
    have hh := hq e
    cases hr : r.1 e <;> cases hs : r.2 e <;>
      cases hx : q.1 e <;> cases hy : q.2 e <;>
      simp [hr,hs,hx,hy,multiplicity] at he hh ⊢
  · apply openGraph_mono
    intro e he
    have hh := hq e
    cases hr : r.1 e <;> cases hs : r.2 e <;>
      cases hx : q.1 e <;> cases hy : q.2 e <;>
      simp [hr,hs,hx,hy,multiplicity] at he hh ⊢

private lemma face_reverse {E : Type*} (r q : (E → Bool) × (E → Bool))
    (hq : Face r q) : Face r (q.2,q.1) := by
  intro e
  simpa [multiplicity,add_comm] using hq e

/-- Every graph in the forced/allowed interval is realized by an actual
configuration in the same multiplicity face, with a complementary partner. -/
private lemma realize_interval {V E : Type*} (ends : E → V × V)
    (r : (E → Bool) × (E → Bool)) (K : SimpleGraph V)
    (hHK : forced ends r ≤ K) (hKU : K ≤ allowed ends r) :
    ∃ q : (E → Bool) × (E → Bool), Face r q ∧ openGraph ends q.1 = K := by
  classical
  let ω : E → Bool := fun e =>
    if r.1 e = r.2 e then r.1 e else decide (K.Adj (ends e).1 (ends e).2)
  let η : E → Bool := fun e => if r.1 e = r.2 e then r.1 e else !(ω e)
  refine ⟨(ω,η),?_,?_⟩
  · intro e
    dsimp only
    cases hr : r.1 e <;> cases hs : r.2 e <;>
      by_cases hk : K.Adj (ends e).1 (ends e).2 <;>
      simp [ω,η,hr,hs,multiplicity,hk]
  · apply le_antisymm
    · intro x y hxy
      rcases hxy with ⟨hne,⟨e,he,hexy⟩ | ⟨e,he,heyx⟩⟩
      · have hx := congrArg Prod.fst hexy
        have hy := congrArg Prod.snd hexy
        dsimp at hx hy
        subst x; subst y
        by_cases heq : r.1 e = r.2 e
        · have hforce : r.1 e && r.2 e = true := by
            simpa [ω,heq] using he
          exact hHK ⟨hne,Or.inl ⟨e,hforce,rfl⟩⟩
        · simpa [ω,heq] using he
      · have hx := congrArg Prod.fst heyx
        have hy := congrArg Prod.snd heyx
        dsimp at hx hy
        subst x; subst y
        by_cases heq : r.1 e = r.2 e
        · have hforce : r.1 e && r.2 e = true := by
            simpa [ω,heq] using he
          exact hHK ⟨hne,Or.inr ⟨e,hforce,rfl⟩⟩
        · have hadj : K.Adj (ends e).1 (ends e).2 := by simpa [ω,heq] using he
          exact hadj.symm
    · intro x y hxy
      have hu := hKU hxy
      rcases hu with ⟨hne,⟨e,he,hexy⟩ | ⟨e,he,heyx⟩⟩
      · have hopen : ω e = true := by
          by_cases heq : r.1 e = r.2 e
          · have hr : r.1 e = true := by simpa only [← heq,Bool.or_self] using he
            simp only [ω,if_pos heq,hr]
          · have hadj : K.Adj (ends e).1 (ends e).2 := by
              rw [hexy]
              exact hxy
            simp [ω,heq,hadj]
        exact ⟨hne,Or.inl ⟨e,hopen,hexy⟩⟩
      · have hopen : ω e = true := by
          by_cases heq : r.1 e = r.2 e
          · have hr : r.1 e = true := by simpa only [← heq,Bool.or_self] using he
            simp only [ω,if_pos heq,hr]
          · have hadj : K.Adj (ends e).1 (ends e).2 := by
              rw [heyx]
              exact hxy.symm
            simp [ω,heq,hadj]
        exact ⟨hne,Or.inr ⟨e,hopen,heyx⟩⟩

private lemma swap_restrictions {V E : Type*} (ends : E → V × V) (A : Set V)
    (q : (E → Bool) × (E → Bool)) :
    let S : Set E := {e | (ends e).1 ∈ A ∨ (ends e).2 ∈ A}
    ThreeTerminalWiredSeparation.touchGraph (openGraph ends (swap S q).1) A =
      ThreeTerminalWiredSeparation.touchGraph (openGraph ends q.2) A ∧
    sideGraph (openGraph ends (swap S q).1) Aᶜ = sideGraph (openGraph ends q.1) Aᶜ := by
  classical
  dsimp only
  constructor
  · ext x y
    constructor
    · rintro ⟨⟨hne,hh⟩,hA⟩
      refine ⟨⟨hne,?_⟩,hA⟩
      rcases hh with ⟨e,he,hexy⟩ | ⟨e,he,heyx⟩
      · have heA : (ends e).1 ∈ A ∨ (ends e).2 ∈ A := by simpa [hexy] using hA
        exact Or.inl ⟨e,by simpa [swap,heA] using he,hexy⟩
      · have heA : (ends e).1 ∈ A ∨ (ends e).2 ∈ A := by simpa [heyx,or_comm] using hA
        exact Or.inr ⟨e,by simpa [swap,heA] using he,heyx⟩
    · rintro ⟨⟨hne,hh⟩,hA⟩
      refine ⟨⟨hne,?_⟩,hA⟩
      rcases hh with ⟨e,he,hexy⟩ | ⟨e,he,heyx⟩
      · have heA : (ends e).1 ∈ A ∨ (ends e).2 ∈ A := by simpa [hexy] using hA
        exact Or.inl ⟨e,by simpa [swap,heA] using he,hexy⟩
      · have heA : (ends e).1 ∈ A ∨ (ends e).2 ∈ A := by simpa [heyx,or_comm] using hA
        exact Or.inr ⟨e,by simpa [swap,heA] using he,heyx⟩
  · ext x y
    constructor
    · rintro ⟨⟨hne,hh⟩,hx,hy⟩
      refine ⟨⟨hne,?_⟩,hx,hy⟩
      rcases hh with ⟨e,he,hexy⟩ | ⟨e,he,heyx⟩
      · have heA : ¬ ((ends e).1 ∈ A ∨ (ends e).2 ∈ A) := by simpa [hexy] using not_or.mpr ⟨hx,hy⟩
        exact Or.inl ⟨e,by simpa [swap,heA] using he,hexy⟩
      · have heA : ¬ ((ends e).1 ∈ A ∨ (ends e).2 ∈ A) := by simpa [heyx] using not_or.mpr ⟨hy,hx⟩
        exact Or.inr ⟨e,by simpa [swap,heA] using he,heyx⟩
    · rintro ⟨⟨hne,hh⟩,hx,hy⟩
      refine ⟨⟨hne,?_⟩,hx,hy⟩
      rcases hh with ⟨e,he,hexy⟩ | ⟨e,he,heyx⟩
      · have heA : ¬ ((ends e).1 ∈ A ∨ (ends e).2 ∈ A) := by simpa [hexy] using not_or.mpr ⟨hx,hy⟩
        exact Or.inl ⟨e,by simpa [swap,heA] using he,hexy⟩
      · have heA : ¬ ((ends e).1 ∈ A ∨ (ends e).2 ∈ A) := by simpa [heyx] using not_or.mpr ⟨hy,hx⟩
        exact Or.inr ⟨e,by simpa [swap,heA] using he,heyx⟩

private lemma swap_modes {V E : Type*} (ends : E → V × V)
    (r q : (E → Bool) × (E → Bool)) (a b c : V)
    (ha : ¬ (forced ends r).Reachable b a) (hc : ¬ (forced ends r).Reachable b c)
    (hsep : ¬ (sideGraph (allowed ends r) {v | ¬ (forced ends r).Reachable b v}).Reachable a c)
    (hq : Face r q) :
    let A := {v | (sideGraph (allowed ends r) {v | ¬ (forced ends r).Reachable b v}).Reachable a v}
    let S : Set E := {e | (ends e).1 ∈ A ∨ (ends e).2 ∈ A}
    (graphMode (openGraph ends q.1) a b c = .separate ∧
      graphMode (openGraph ends q.2) a b c = .all) ↔
    (graphMode (openGraph ends (swap S q).1) a b c = .ab ∧
      graphMode (openGraph ends (swap S q).2) a b c = .bc) := by
  classical
  let A := {v | (sideGraph (allowed ends r) {v | ¬ (forced ends r).Reachable b v}).Reachable a v}
  let S : Set E := {e | (ends e).1 ∈ A ∨ (ends e).2 ∈ A}
  have mode (q : (E → Bool) × (E → Bool)) (hf : Face r q) :=
    (ThreeTerminalWiredSeparation.wired_separation (forced ends r) (allowed ends r)
      (openGraph ends q.1) (face_interval ends r q hf).1 (face_interval ends r q hf).2
      a b c ha hc hsep).2.2.2
  have h1 := mode q hq
  have h2 := mode (q.2,q.1) (face_reverse r q hq)
  have h3 := mode (swap S q) (swap_face S r q hq)
  have h4 := mode ((swap S q).2,(swap S q).1)
    (face_reverse r (swap S q) (swap_face S r q hq))
  have hL1 := (swap_restrictions ends A q).1
  have hR1 := (swap_restrictions ends A q).2
  have hL2 := (swap_restrictions ends A (q.2,q.1)).1
  have hR2 := (swap_restrictions ends A (q.2,q.1)).2
  dsimp only at h1 h2 h3 h4
  change _ ↔ _
  rw [h1,h2,h3,h4]
  change ThreeTerminalWiredSeparation.touchGraph (openGraph ends (swap S q).2) A =
    ThreeTerminalWiredSeparation.touchGraph (openGraph ends q.1) A at hL2
  change sideGraph (openGraph ends (swap S q).2) Aᶜ =
    sideGraph (openGraph ends q.2) Aᶜ at hR2
  rw [hL1,hR1,hL2,hR2]
  by_cases hx : (forced ends r ⊔ ThreeTerminalWiredSeparation.touchGraph (openGraph ends q.1) A).Reachable a b <;>
    by_cases hy : (forced ends r ⊔ sideGraph (openGraph ends q.1) Aᶜ).Reachable b c <;>
    by_cases hz : (forced ends r ⊔ ThreeTerminalWiredSeparation.touchGraph (openGraph ends q.2) A).Reachable a b <;>
    by_cases hw : (forced ends r ⊔ sideGraph (openGraph ends q.2) Aᶜ).Reachable b c <;>
    simp only [A] at hx hy hz hw ⊢ <;> simp [hx,hy,hz,hw]

/-- An ac-free face has equally many ordered (separate,all) and (ab,bc)
pairs. The bijection exchanges one fixed set of actual edge coordinates. -/
theorem face_cancel {V E : Type*} [Fintype E] [DecidableEq E] (ends : E → V × V)
    (r : (E → Bool) × (E → Bool)) (a b c : V)
    (hno : ∀ q, Face r q → graphMode (openGraph ends q.1) a b c ≠ .ac) :
    (Finset.univ.filter fun q : (E → Bool) × (E → Bool) => Face r q ∧
      graphMode (openGraph ends q.1) a b c = .separate ∧
      graphMode (openGraph ends q.2) a b c = .all).card =
    (Finset.univ.filter fun q : (E → Bool) × (E → Bool) => Face r q ∧
      graphMode (openGraph ends q.1) a b c = .ab ∧
      graphMode (openGraph ends q.2) a b c = .bc).card := by
  classical
  have degenerate (hab : (forced ends r).Reachable b a ∨ (forced ends r).Reachable b c) :
      ∀ q, Face r q →
      graphMode (openGraph ends q.1) a b c ≠ .separate ∧
      ¬ (graphMode (openGraph ends q.1) a b c = .ab ∧
        graphMode (openGraph ends q.2) a b c = .bc) := by
    intro q hf
    have hi := face_interval ends r q hf
    have hj := face_interval ends r (q.2,q.1) (face_reverse r q hf)
    rcases hab with hab | hbc
    · have h1 := (hab.mono hi.1).symm
      have h2 := (hab.mono hj.1).symm
      constructor
      · by_cases hx : (openGraph ends q.1).Reachable b c <;> simp [graphMode,h1,hx]
      · by_cases hx : (openGraph ends q.2).Reachable b c <;> simp [graphMode,h2,hx]
    · have h1 := hbc.mono hi.1
      constructor
      · by_cases hx : (openGraph ends q.1).Reachable a b <;> simp [graphMode,h1,hx]
      · by_cases hx : (openGraph ends q.1).Reachable a b <;> simp [graphMode,h1,hx]
  by_cases ha : (forced ends r).Reachable b a
  · have hl : ∀ q, ¬ (Face r q ∧ graphMode (openGraph ends q.1) a b c = .separate ∧
        graphMode (openGraph ends q.2) a b c = .all) := by
      rintro q ⟨hf,hm,_⟩
      exact (degenerate (Or.inl ha) q hf).1 hm
    have hr : ∀ q, ¬ (Face r q ∧ graphMode (openGraph ends q.1) a b c = .ab ∧
        graphMode (openGraph ends q.2) a b c = .bc) := by
      rintro q ⟨hf,hm⟩
      exact (degenerate (Or.inl ha) q hf).2 hm
    simp [hl,hr]
  by_cases hc : (forced ends r).Reachable b c
  · have hl : ∀ q, ¬ (Face r q ∧ graphMode (openGraph ends q.1) a b c = .separate ∧
        graphMode (openGraph ends q.2) a b c = .all) := by
      rintro q ⟨hf,hm,_⟩
      exact (degenerate (Or.inr hc) q hf).1 hm
    have hr : ∀ q, ¬ (Face r q ∧ graphMode (openGraph ends q.1) a b c = .ab ∧
        graphMode (openGraph ends q.2) a b c = .bc) := by
      rintro q ⟨hf,hm⟩
      exact (degenerate (Or.inr hc) q hf).2 hm
    simp [hl,hr]
  have hHU : forced ends r ≤ allowed ends r :=
    (face_interval ends r r (fun _ => rfl)).1.trans
      (face_interval ends r r (fun _ => rfl)).2
  have hsep : ¬ (sideGraph (allowed ends r) {v | ¬ (forced ends r).Reachable b v}).Reachable a c := by
    intro hh
    obtain ⟨K,hHK,hKU,hmode⟩ :=
      (interval_ac_iff_avoiding_forced_component (forced ends r) (allowed ends r) hHU a b c ha hc).mpr hh
    obtain ⟨q,hf,hqK⟩ := realize_interval ends r K hHK hKU
    exact hno q hf (hqK ▸ hmode)
  let A := {v | (sideGraph (allowed ends r) {v | ¬ (forced ends r).Reachable b v}).Reachable a v}
  let S : Set E := {e | (ends e).1 ∈ A ∨ (ends e).2 ∈ A}
  apply Finset.card_bij (fun q _ => swap S q)
  · intro q hq
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hq ⊢
    exact ⟨swap_face S r q hq.1,(swap_modes ends r q a b c ha hc hsep hq.1).mp hq.2⟩
  · intro q hq q' hq' heq
    have hh := congrArg (swap S) heq
    simpa only [swap_swap] using hh
  · intro q hq
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hq
    refine ⟨swap S q,?_,swap_swap S q⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨swap_face S r q hq.1,?_⟩
    have hh := (swap_modes ends r (swap S q) a b c ha hc hsep
      (swap_face S r q hq.1)).mpr
    apply hh
    change graphMode (openGraph ends (swap S (swap S q)).1) a b c = .ab ∧
      graphMode (openGraph ends (swap S (swap S q)).2) a b c = .bc
    simpa only [swap_swap] using hq.2

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch.face_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms face_cancel

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSwitch
