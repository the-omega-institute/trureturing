/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonJointMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonJointMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reconstruct every literal marked signed ribbon boundary observable from one global family of quotient-code mixed-state moments. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Perm.Cycle.Factors
import D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Function.Basic
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Quotient
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments

section FlagPartialDual

open Finset Relation
open scoped BigOperators

variable {E X : Type*}

def switch (t s : E → Bool) : E → Bool := fun e => Bool.xor (t e) (s e)
variable {R : Type*} [CommSemiring R] [Fintype E] [DecidableEq E]

end FlagPartialDual

section BouquetChart

open Finset Relation
open scoped BigOperators

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary

variable {n : ℕ} {E : Type*}
variable [Fintype E]
def selected (s : E → Bool) : Finset E :=
  univ.filter (fun e=>s e=true)

private theorem mem_selected_iff (s : E → Bool) (e : E) : e ∈ selected s ↔ s e=true := by
  simp [selected]

variable [DecidableEq E]

end BouquetChart

section ForestParity

open Relation

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem involution_even_finset (f : X → X) (hi : Function.Involutive f)
    (hf : ∀ x, f x ≠ x) (s : Finset X) (hs : ∀ x∈s, f x∈s) :
    Even s.card := by
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases h : s.Nonempty
  · obtain ⟨a,ha⟩ := h
    have hb : f a ∈ s := hs _ ha
    have hba : f a ≠ a := hf a
    have hab : a ≠ f a := hba.symm
    let t := (s.erase a).erase (f a)
    have hb' : f a ∈ s.erase a := Finset.mem_erase.mpr ⟨hba,hb⟩
    have hta : t.card + 2 = s.card := by
      have h1 := Finset.card_erase_add_one ha
      have h2 := Finset.card_erase_add_one hb'
      dsimp [t]
      omega
    have hsub : t ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _),?_⟩
      intro h'
      have h1 : a ∈ t := h' ▸ ha
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp h1).2).1 rfl
    have hstab : ∀ x∈t, f x∈t := by
      intro x hx
      obtain ⟨hxB,hx⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxA,hx⟩ := Finset.mem_erase.mp hx
      apply Finset.mem_erase.mpr
      refine ⟨fun h => hxA (hi.injective h),Finset.mem_erase.mpr ⟨?_,hs x hx⟩⟩
      intro hx'
      apply hxB
      rw [← hi x,hx']
    obtain ⟨m,hm⟩ := ih t hsub hstab
    exact ⟨m+1,by omega⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    subst s
    simp

/-- Matchings on opposite sides of an isolated proposed bridge impose
incompatible parity. In the second matching only the marked flag is
allowed to leave the cut. -/
private theorem matching_cut_impossible (G A : X → X) (hGi : Function.Involutive G)
    (hAi : Function.Involutive A) (hGf : ∀ x, G x ≠ x) (hAf : ∀ x, A x ≠ x)
    (s : Finset X) (a : X) (ha : a∈s) (hb : A a∉s)
    (hG : ∀ x∈s, G x∈s) (hA : ∀ x∈s, x≠a → A x∈s) : False := by
  obtain ⟨m,hm⟩ := involution_even_finset G hGi hGf s hG
  have hdel : ∀ x∈s.erase a, A x∈s.erase a := by
    intro x hx
    obtain ⟨hne,hx⟩ := Finset.mem_erase.mp hx
    refine Finset.mem_erase.mpr ⟨?_,hA x hx hne⟩
    intro hx'
    apply hb
    rw [← hx',hAi]
    exact hx
  obtain ⟨k,hk⟩ := involution_even_finset A hAi hAf (s.erase a) hdel
  have hs := Finset.card_erase_add_one ha
  omega

def matchStep (G A : X → X) (del : X → Prop) (x y : X) : Prop :=
  y=G x ∨ (¬del x ∧ y=A x)

def matchConn (G A : X → X) (del : X → Prop) :=
  EqvGen (matchStep G A del)

private theorem matchConn_mono (G A : X → X) {P Q : X → Prop}
    (h : ∀ x, Q x → P x) {x y : X} :
    matchConn G A P x y → matchConn G A Q x y := by
  intro hxy
  induction hxy with
  | rel x y hxy =>
    apply EqvGen.rel
    rcases hxy with hg|⟨hp,ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨fun hy=>hp (h x hy),ha⟩
  | refl x => exact EqvGen.refl x
  | symm x y hxy ih => exact EqvGen.symm _ _ ih
  | trans x y z hxy hyz ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

/-- No symmetric deletion of one edge per original component can
separate the endpoints of any deleted edge. The hypothesis is local:
only vertices in that edge's original component matter. -/
private theorem removed_edge_endpoints_connected (G A : X → X)
    (hGi : Function.Involutive G) (hAi : Function.Involutive A)
    (hGf : ∀ x,G x ≠ x) (hAf : ∀ x,A x ≠ x)
    (del : X → Prop) (a : X)
    (huniq : ∀ x, matchConn G A (fun _=>False) a x → del x → x=a ∨ x=A a) :
    matchConn G A del a (A a) := by
  classical
  by_contra hn
  let s : Finset X := Finset.univ.filter (matchConn G A del a)
  have hmem (x:X) : x∈s ↔ matchConn G A del a x := by simp [s]
  have ha : a∈s := (hmem a).mpr (.refl a)
  have hb : A a∉s := fun hx=>hn ((hmem _).mp hx)
  apply matching_cut_impossible G A hGi hAi hGf hAf s a ha hb
  · intro x hx
    apply (hmem _).mpr
    exact .trans _ _ _ ((hmem _).mp hx) (.rel _ _ (Or.inl rfl))
  · intro x hx hxa
    apply (hmem _).mpr
    have hconn := (hmem _).mp hx
    have hnd : ¬del x := fun hdx => (huniq x
      (matchConn_mono G A (fun _ h=>h.elim) hconn) hdx).elim hxa
      (fun h => hb (h ▸ hx))
    exact .trans _ _ _ hconn (.rel _ _ (Or.inr ⟨hnd,rfl⟩))

/-- Delete one matching edge per affected original component, and every
old component is preserved as a literal equivalence relation. -/
private theorem deletion_preserves_components (G A : X → X)
    (hGi : Function.Involutive G) (hAi : Function.Involutive A)
    (hGf : ∀ x,G x ≠ x) (hAf : ∀ x,A x ≠ x)
    (del : X → Prop)
    (huniq : ∀ a x, del a → matchConn G A (fun _=>False) a x → del x → x=a ∨ x=A a)
    (x y : X) :
    matchConn G A del x y ↔ matchConn G A (fun _=>False) x y := by
  refine ⟨matchConn_mono G A (fun _ h=>h.elim),?_⟩
  intro h
  induction h with
  | rel x y hxy =>
    rcases hxy with hg|⟨_,rfl⟩
    · exact .rel _ _ (.inl hg)
    · by_cases hdel : del x
      · exact removed_edge_endpoints_connected G A hGi hAi hGf hAf del x (fun z=>huniq x z hdel)
      · exact .rel _ _ (.inr ⟨hdel,rfl⟩)
  | refl x => exact .refl x
  | symm x y hxy ih => exact .symm _ _ ih
  | trans x y z hxy hyz ih1 ih2 => exact .trans _ _ _ ih1 ih2

end ForestParity

section ForestSwitch

open Relation

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev wholeConn (G A : X→X) := matchConn G A (fun _=>False)

def addedJoin (R : X→X→Prop) (a b : X) (x y : X) :=
  EqvGen (fun i j => R i j ∨ (i=a ∧ j=b)) x y

private theorem step_to_whole (G A : X→X) (x : X) : wholeConn G A x (A x) :=
  .rel _ _ (.inr ⟨id,rfl⟩)

private theorem eqvGen_transfer {R S : X→X→Prop} (hf : ∀ x y, R x y → S x y)
    (hs : Equivalence S) (x y : X) (h : EqvGen R x y) : S x y := by
  induction h with
  | rel x y h => exact hf x y h
  | refl x => exact hs.refl x
  | symm x y _ ih => exact hs.symm ih
  | trans x y z _ _ ih1 ih2 => exact hs.trans ih1 ih2

private theorem eqvGen_is_equivalence (R : X→X→Prop) : Equivalence (EqvGen R) :=
  ⟨.refl, fun h=>.symm _ _ h, fun h g=>.trans _ _ _ h g⟩

/-- Switching the two matching edges of two different boundary circles
is exactly adjoining the connection between those circles. Both signs
satisfy the same assumptions, even when an A-edge is also a G-edge. -/
private theorem match_switch_join (G A A' : X→X)
    (hGi : Function.Involutive G) (hAi : Function.Involutive A)
    (hGf : ∀ x,G x≠x) (hAf : ∀ x,A x≠x)
    (a b : X) (hab : ¬wholeConn G A a b)
    (hsame : ∀ x, ¬(x=a ∨ x=A a ∨ x=b ∨ x=A b) → A' x = A x)
    (hcrossA : ∀ x, x=a ∨ x=A a → A' x=b ∨ A' x=A b)
    (hcrossB : ∀ x, x=b ∨ x=A b → A' x=a ∨ A' x=A a)
    (x y : X) :
    wholeConn G A' x y ↔ addedJoin (wholeConn G A) a b x y := by
  let del : X→Prop := fun z=>z=a ∨ z=A a ∨ z=b ∨ z=A b
  let old := wholeConn G A
  let new := wholeConn G A'
  let J := addedJoin old a b
  have eqold : Equivalence old := eqvGen_is_equivalence _
  have eqnew : Equivalence new := eqvGen_is_equivalence _
  have eqJ : Equivalence J := eqvGen_is_equivalence _
  have hA : ∀ z, z=a ∨ z=A a → old a z := by
    rintro z (rfl|rfl)
    · exact eqold.refl _
    · exact step_to_whole _ _ _
  have hB : ∀ z, z=b ∨ z=A b → old b z := by
    rintro z (rfl|rfl)
    · exact eqold.refl _
    · exact step_to_whole _ _ _
  have hnoAB : ∀ i j, (i=a ∨ i=A a) → (j=b ∨ j=A b) → ¬old i j := by
    intro i j hi hj hij
    exact hab (eqold.trans (hA i hi) (eqold.trans hij (eqold.symm (hB j hj))))
  have huniq : ∀ i j, del i → old i j → del j → j=i ∨ j=A i := by
    intro i j hi hij hj
    have his : (i=a ∨ i=A a) ∨ (i=b ∨ i=A b) := by
      rcases hi with h|h|h|h
      exacts [.inl (.inl h),.inl (.inr h),.inr (.inl h),.inr (.inr h)]
    have hjs : (j=a ∨ j=A a) ∨ (j=b ∨ j=A b) := by
      rcases hj with h|h|h|h
      exacts [.inl (.inl h),.inl (.inr h),.inr (.inl h),.inr (.inr h)]
    rcases his with hi|hi
    · rcases hjs with hj|hj
      · rcases hi with rfl|rfl
        · exact hj
        · rw [hAi]
          exact hj.symm
      · exact (hnoAB i j hi hj hij).elim
    · rcases hjs with hj|hj
      · exact (hnoAB j i hj hi (eqold.symm hij)).elim
      · rcases hi with rfl|rfl
        · exact hj
        · rw [hAi]
          exact hj.symm
  have holdnew : ∀ i j, old i j → new i j := by
    intro i j h
    have h0 := (deletion_preserves_components G A hGi hAi hGf hAf del huniq i j).mpr h
    apply eqvGen_transfer _ eqnew i j h0
    intro k l hkl
    rcases hkl with hG|⟨hn,hA⟩
    · exact .rel _ _ (.inl hG)
    · exact .rel _ _ (.inr ⟨id,hA.trans (hsame k hn).symm⟩)
  have hjnew : new a b := eqnew.trans (step_to_whole G A' a)
    (holdnew (A' a) b (eqold.symm (hB _ (hcrossA a (.inl rfl)))))
  have htoJ : ∀ i j, old i j → J i j := fun i j h => .rel _ _ (.inl h)
  have hjJ : J a b := .rel _ _ (.inr ⟨rfl,rfl⟩)
  have hJcross : ∀ i j, (i=a ∨ i=A a) → (j=b ∨ j=A b) → J i j := by
    intro i j hi hj
    exact eqJ.trans (htoJ _ _ (eqold.symm (hA i hi))) (eqJ.trans hjJ (htoJ _ _ (hB j hj)))
  constructor
  · apply eqvGen_transfer _ eqJ
    intro i j hij
    rcases hij with hg|⟨_,hA'⟩
    · exact htoJ _ _ (.rel _ _ (.inl hg))
    · subst j
      by_cases hi : del i
      · rcases hi with h|h|h|h
        · exact hJcross _ _ (.inl h) (hcrossA _ (.inl h))
        · exact hJcross _ _ (.inr h) (hcrossA _ (.inr h))
        · exact eqJ.symm (hJcross _ _ (hcrossB _ (.inl h)) (.inl h))
        · exact eqJ.symm (hJcross _ _ (hcrossB _ (.inr h)) (.inr h))
      · rw [hsame i hi]
        exact htoJ _ _ (step_to_whole _ _ _)
  · apply eqvGen_transfer _ eqnew
    intro i j hij
    rcases hij with h|⟨rfl,rfl⟩
    · exact holdnew _ _ h
    · exact hjnew

end ForestSwitch

section ForestIterate

open Relation
variable {X : Type*} [Fintype X] [DecidableEq X]

def graphJoin (R : X→X→Prop) (l : List (X×X)) (x y : X) :=
  EqvGen (fun i j => R i j ∨ (i,j) ∈ l) x y

private theorem graphJoin_cons (R : X→X→Prop) (a b : X) (l : List (X×X)) (x y : X) :
    graphJoin (addedJoin R a b) l x y ↔ graphJoin R ((a,b)::l) x y := by
  have he' : Equivalence (graphJoin R ((a,b)::l)) := eqvGen_is_equivalence _
  have he : Equivalence (graphJoin (addedJoin R a b) l) := eqvGen_is_equivalence _
  constructor
  · apply eqvGen_transfer _ he'
    intro i j h
    rcases h with h|h
    · apply eqvGen_transfer _ he' i j h
      intro i j h
      rcases h with h|⟨rfl,rfl⟩
      · exact .rel _ _ (.inl h)
      · exact .rel _ _ (.inr (List.mem_cons_self ..))
    · exact .rel _ _ (.inr (List.mem_cons_of_mem _ h))
  · apply eqvGen_transfer _ he
    intro i j h
    rcases h with h|h
    · exact .rel _ _ (.inl (.rel _ _ (.inl h)))
    · rcases List.mem_cons.mp h with h|h
      · cases h
        exact .rel _ _ (.inl (.rel _ _ (.inr ⟨rfl,rfl⟩)))
      · exact .rel _ _ (.inr h)

private theorem graphJoin_congr {R S : X→X→Prop} (h : ∀ x y, R x y ↔ S x y)
    (l : List (X×X)) (x y : X) : graphJoin R l x y ↔ graphJoin S l x y := by
  have he' : Equivalence (graphJoin S l) := eqvGen_is_equivalence _
  have he : Equivalence (graphJoin R l) := eqvGen_is_equivalence _
  constructor
  · exact eqvGen_transfer (fun i j hh=>.rel _ _ (hh.imp (h i j).mp id)) he' x y
  · exact eqvGen_transfer (fun i j hh=>.rel _ _ (hh.imp (h i j).mpr id)) he x y

end ForestIterate

section CycleOrientation

open Relation

variable {X : Type*} [Fintype X] [DecidableEq X]

def permInvol (f : X→X) (h : Function.Involutive f) : Equiv.Perm X where
  toFun := f
  invFun := f
  left_inv := h
  right_inv := h
private theorem permInvol_inv (f : X→X) (h : Function.Involutive f) :
    (permInvol f h)⁻¹ = permInvol f h := by
  ext x
  rfl

def cycleTurn (G A : X→X) (hg : Function.Involutive G) (ha : Function.Involutive A) :=
  permInvol G hg * permInvol A ha

def powerOrbit (T : Equiv.Perm X) (x y : X) : Prop := ∃ k : ℤ, (T^k) x = y

private theorem powerOrbit_equiv (T : Equiv.Perm X) : Equivalence (powerOrbit T) := by
  constructor
  · intro x
    exact ⟨0,by simp⟩
  · rintro x y ⟨k,rfl⟩
    refine ⟨-k,?_⟩
    rw [← Equiv.Perm.mul_apply,← zpow_add]
    simp
  · rintro x y z ⟨k,rfl⟩ ⟨l,rfl⟩
    exact ⟨l+k,by rw [zpow_add,Equiv.Perm.mul_apply]⟩

private theorem reflect_power (G A : X→X) (hg : Function.Involutive G)
    (ha : Function.Involutive A) (k : ℤ) (x : X) :
    A (((cycleTurn G A hg ha)^k) x) = ((cycleTurn G A hg ha)^(-k)) (A x) := by
  let B := permInvol A ha
  let J := permInvol G hg
  let T := cycleTurn G A hg ha
  have hB : B⁻¹=B := permInvol_inv A ha
  have hJ : J⁻¹=J := permInvol_inv G hg
  have hc : B*T*B⁻¹=T⁻¹ := by
    change B*(J*B)*B⁻¹=(J*B)⁻¹
    rw [mul_inv_rev,hJ,mul_assoc B (J*B) B⁻¹,mul_assoc J B B⁻¹,
      mul_inv_cancel,mul_one,hB]
  have hpow : B*T^k*B⁻¹=T^(-k) := by rw [← conj_zpow,hc,inv_zpow,zpow_neg]
  have hconj : B*T^k = T^(-k)*B := by rw [← hpow,mul_assoc,inv_mul_cancel,mul_one]
  exact congrArg (fun U : Equiv.Perm X => U x) hconj

/-- A gap and two fixed-point-free reflection matchings force the two
orientations of each alternating circle to be distinct rotation orbits. -/
private theorem orientation_orbits_disjoint (G A : X→X) (hg : Function.Involutive G)
    (ha : Function.Involutive A) (hG : ∀ x,G x≠x) (hA : ∀ x,A x≠x) (x : X) :
    ¬powerOrbit (cycleTurn G A hg ha) x (A x) := by
  rintro ⟨k,hk⟩
  let T := cycleTurn G A hg ha
  change (T^k) x = A x at hk
  have haTk (l : ℤ) : A ((T^l) x) = (T^(k-l)) x := by
    rw [show A ((T^l) x) = (T^(-l)) (A x) from reflect_power G A hg ha l x,
      ← hk,← Equiv.Perm.mul_apply,← zpow_add]
    congr 2
    omega
  have hgTk (l : ℤ) : G ((T^l) x) = (T^(k-l+1)) x := by
    have h : G ((T^l) x) = T (A ((T^l) x)) := by
      change _ = G (A (A ((T^l) x)))
      rw [ha]
    rw [h,haTk,← Equiv.Perm.mul_apply]
    have hprod : T * T^(k-l) = T^(k-l+1) := by
      calc
        T * T^(k-l) = T^(1:ℤ)*T^(k-l) := by simp
        _ = _ := by rw [← zpow_add]; congr 1; omega
    rw [hprod]
  by_cases h : k % 2=0
  · have hh : k-k/2=k/2 := by omega
    exact hA _ (by rw [haTk,hh])
  · have hh : k-(k+1)/2+1=(k+1)/2 := by omega
    exact hG _ (by rw [hgTk,hh])


private theorem reflect_orbit (G A : X→X) (hg : Function.Involutive G)
    (ha : Function.Involutive A) {x y : X} :
    powerOrbit (cycleTurn G A hg ha) x y → powerOrbit (cycleTurn G A hg ha) (A x) (A y) := by
  rintro ⟨k,rfl⟩
  exact ⟨-k,(reflect_power G A hg ha k x).symm⟩

/-- Every connected flag is in one of the two oriented rotation orbits. -/
private theorem connected_two_orbits (G A : X→X) (hg : Function.Involutive G)
    (ha : Function.Involutive A) {x y : X} (hxy : wholeConn G A x y) :
    powerOrbit (cycleTurn G A hg ha) x y ∨ powerOrbit (cycleTurn G A hg ha) (A x) y := by
  let T := cycleTurn G A hg ha
  let R (x y : X) := powerOrbit T x y ∨ powerOrbit T (A x) y
  have he := powerOrbit_equiv T
  have rf : ∀ {x y}, powerOrbit T x y → powerOrbit T (A x) (A y) :=
    fun {_ _} => reflect_orbit G A hg ha
  have heR : Equivalence R := by
    constructor
    · exact fun x=>.inl (he.refl x)
    · intro x y h
      rcases h with h|h
      · exact .inl (he.symm h)
      · have hw := rf (he.symm h)
        rw [ha] at hw
        exact .inr hw
    · intro x y z hxy hyz
      rcases hxy with h|h <;> rcases hyz with k|k
      · exact .inl (he.trans h k)
      · exact .inr (he.trans (rf h) k)
      · exact .inr (he.trans h k)
      · have hw := rf h
        rw [ha] at hw
        exact .inl (he.trans hw k)
  change R x y
  apply eqvGen_transfer _ heR x y hxy
  intro i j h
  rcases h with rfl|⟨_,rfl⟩
  · refine .inr ⟨1,?_⟩
    rw [zpow_one]
    change G (A (A i)) = G i
    rw [ha]
  · exact .inr (he.refl _)

/-- Explicit chart on a connected alternating flag system, using an
intrinsic oriented orbit for ports. The bit is the input/output flag. -/
noncomputable def orientedFlagEquiv (G A : X→X) (hg : Function.Involutive G)
    (ha : Function.Involutive A) (hG : ∀ x,G x≠x) (hA : ∀ x,A x≠x)
    (x : X) (hc : ∀ y, wholeConn G A x y) :
    {y : X // powerOrbit (cycleTurn G A hg ha) x y} × Bool ≃ X := by
  classical
  let T := cycleTurn G A hg ha
  let P := {y : X // powerOrbit T x y}
  let f : P×Bool → X := fun q=>if q.2 then A q.1.1 else q.1.1
  have hd (y : X) (hy : powerOrbit T x y) : ¬powerOrbit T x (A y) := by
    intro hz
    have ht := (powerOrbit_equiv T).trans hz ((powerOrbit_equiv T).symm
      (reflect_orbit G A hg ha hy))
    exact orientation_orbits_disjoint G A hg ha hG hA x ht
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨u,a⟩ ⟨v,b⟩ h
    cases a <;> cases b
    · have hh : u.1=v.1 := h
      rw [Subtype.ext hh]
    · have hh : u.1=A v.1 := h
      exact (hd v.1 v.2 (hh ▸ u.2)).elim
    · have hh : A u.1=v.1 := h
      exact (hd u.1 u.2 (hh.symm ▸ v.2)).elim
    · have hh : A u.1=A v.1 := h
      rw [Subtype.ext (ha.injective hh)]
  · intro y
    rcases connected_two_orbits G A hg ha (hc y) with h|h
    · exact ⟨(⟨y,h⟩,false),rfl⟩
    · have hh := reflect_orbit G A hg ha h
      rw [ha] at hh
      exact ⟨(⟨A y,hh⟩,true),ha y⟩

end CycleOrientation

section CycleNumbering

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open Equiv.Perm
open Lean

variable {X : Type*} [Fintype X] [DecidableEq X]

structure OrbitNumbering (T : Equiv.Perm X) (x : X) where
  n : ℕ
  ports : Fin (n+1) ≃ {y : X // powerOrbit T x y}
  next : ∀ i : Fin (n+1), (ports (cyclicNext i)).1 = T (ports i).1

/-- Number both genuine alternating cycles and the degenerate two-flag
cycle using the actual cyclic successor, not a supplied order. -/
noncomputable def rotation_numbering (T : Equiv.Perm X) (x : X) :
    OrbitNumbering T x := by
  classical
  by_cases hx : T x=x
  · let f : Fin 1 → {y : X // powerOrbit T x y} := fun _=>⟨x,(powerOrbit_equiv T).refl x⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b _
        exact Subsingleton.elim a b
      · rintro ⟨y,⟨k,hk⟩⟩
        refine ⟨0,Subtype.ext ?_⟩
        rw [zpow_apply_eq_self_of_apply_eq_self hx] at hk
        exact hk
    exact ⟨0,Equiv.ofBijective f hf,fun _=>hx.symm⟩
  · let c := (T.cycleOf x).support.card
    have hc : 1≤c := by
      have h := Equiv.Perm.two_le_card_support_cycleOf_iff.mpr hx
      exact le_trans (by decide) h
    have hlen : c-1+1=c := Nat.sub_add_cancel hc
    let f : Fin (c-1+1) → {y : X // powerOrbit T x y} :=
      fun i=>⟨(T^i.val) x,⟨(i.val:ℤ),by rw [zpow_natCast]⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        have he : (T^(i.val:ℤ)) x = (T^(j.val:ℤ)) x := by
          rw [zpow_natCast,zpow_natCast]
          exact congrArg Subtype.val hij
        have hm := (Equiv.Perm.zpow_eq_zpow_on_iff T hx).mp he
        have hi : (i.val:ℤ) < (c:ℤ) := by exact_mod_cast (show i.val < c from i.isLt.trans_le (le_of_eq hlen))
        have hj : (j.val:ℤ) < (c:ℤ) := by exact_mod_cast (show j.val < c from j.isLt.trans_le (le_of_eq hlen))
        change (i.val:ℤ) % (c:ℤ) = (j.val:ℤ) % (c:ℤ) at hm
        rw [Int.emod_eq_of_lt (by omega) hi, Int.emod_eq_of_lt (by omega) hj] at hm
        exact Fin.ext (by exact_mod_cast hm)
      · intro y
        have ho : Equiv.Perm.SameCycle T x y.val := y.property
        obtain ⟨i,hi,he⟩ := ho.exists_pow_eq_of_mem_support (Equiv.Perm.mem_support.mpr hx)
        refine ⟨⟨i,by rw [hlen]; exact hi⟩,Subtype.ext he⟩
    refine ⟨c-1,Equiv.ofBijective f hf,?_⟩
    intro i
    change (T^((i.val+1)%(c-1+1))) x = T ((T^i.val) x)
    have hmod : (i.val+1)%(c-1+1) = (i.val+1)%c :=
      congrArg (fun m : ℕ => (i.val+1)%m) hlen
    rw [hmod,Equiv.Perm.pow_mod_card_support_cycleOf_self_apply]
    rw [pow_succ',Equiv.Perm.mul_apply]

end CycleNumbering

section LiteralOrientationChart

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary

variable {X : Type*} [Fintype X] [DecidableEq X]

structure AlternatingFlagChart (G A : X→X) where
  n : ℕ
  chart : Flag n ≃ X
  base : ∀ i : D n, A (chart (inFlag i)) = chart (outFlag i)
  gap : ∀ i : D n, G (chart (outFlag i)) = chart (inFlag (cyclicNext i))

/-- Literal in/out identification for every connected signed flag system,
including the one-port case, constructed from the matching dynamics. -/
noncomputable def alternating_flag_chart (G A : X→X) (hg : Function.Involutive G)
    (ha : Function.Involutive A) (hG : ∀ x,G x≠x) (hA : ∀ x,A x≠x)
    (x : X) (hc : ∀ y, wholeConn G A x y) : AlternatingFlagChart G A := by
  let T := cycleTurn G A hg ha
  let rot := rotation_numbering T x
  let f := (rot.ports.prodCongr (Equiv.refl Bool)).trans (orientedFlagEquiv G A hg ha hG hA x hc)
  refine ⟨rot.n,f,?_,?_⟩
  · intro i
    rfl
  · intro i
    change G (A (rot.ports i).val) = (rot.ports (cyclicNext i)).val
    exact (rot.next i).symm

/-- Which sign the orientation induces is determined by the actual
alternative matching, rather than assumed as part of the chart. -/
private theorem signed_alternative_from_chart (G A : X→X) (C : AlternatingFlagChart G A)
    (i j : D C.n) (b : X→X) (hb : Function.Involutive b)
    (hin : b (C.chart (inFlag i)) = C.chart (inFlag j) ∨
      b (C.chart (inFlag i)) = C.chart (outFlag j))
    (hout : b (C.chart (outFlag i)) = C.chart (inFlag j) ∨
      b (C.chart (outFlag i)) = C.chart (outFlag j)) :
    ∃ twist : Bool,
      b (C.chart (inFlag i)) = C.chart (if twist then inFlag j else outFlag j) ∧
      b (C.chart (outFlag i)) = C.chart (if twist then outFlag j else inFlag j) := by
  have hd : C.chart (inFlag i) ≠ C.chart (outFlag i) := by
    intro h
    have h' := congrArg Prod.snd (C.chart.injective h)
    contradiction
  rcases hin with h0|h0 <;> rcases hout with h1|h1
  · exact (hd (hb.injective (h0.trans h1.symm))).elim
  · exact ⟨true,h0,h1⟩
  · exact ⟨false,h0,h1⟩
  · exact (hd (hb.injective (h0.trans h1.symm))).elim

end LiteralOrientationChart

section RibbonComponents

open Relation Finset
open scoped BigOperators

variable {C : Type*} {X E : C→Type*}

inductive inComponent (r : ∀ c, X c→X c→Prop) : Sigma X→Sigma X→Prop
  | mk (c : C) (x y : X c) (h : r c x y) : inComponent r ⟨c,x⟩ ⟨c,y⟩
def relSetoid {Y : Type*} (r : Y→Y→Prop) : Setoid Y :=
  ⟨EqvGen r, ⟨.refl,fun h=>.symm _ _ h,fun h g=>.trans _ _ _ h g⟩⟩

private def label (r : ∀ c, X c→X c→Prop) (x : Sigma X) :
    Sigma (fun c=>Quotient (relSetoid (r c))) := ⟨x.1,Quotient.mk _ x.2⟩

private theorem lift_component_path (r : ∀ c, X c→X c→Prop)
    (c:C) {x y:X c} (h:EqvGen (r c) x y) :
    EqvGen (inComponent r) ⟨c,x⟩ ⟨c,y⟩ := by
  induction h with
  | rel x y h => exact .rel _ _ (.mk c x y h)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem component_path_iff (r : ∀ c, X c→X c→Prop) (x y : Sigma X) :
    EqvGen (inComponent r) x y ↔ label r x=label r y := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      cases h with
      | mk c a b h =>
        exact congrArg (Sigma.mk c) (Quotient.sound (.rel a b h : EqvGen (r c) a b))
    | refl x => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rcases x with ⟨i,x⟩; rcases y with ⟨j,y⟩
    intro h
    have hij : i=j := congrArg Sigma.fst h
    subst j
    have hc : Quotient.mk (relSetoid (r i)) x=Quotient.mk (relSetoid (r i)) y := by
      injection h
    exact lift_component_path r i (Quotient.exact hc)

/-- Boundary components themselves decompose, before taking cardinalities. -/
noncomputable def quotient_components (r : ∀ c, X c→X c→Prop) :
    Quotient (relSetoid (inComponent r)) ≃ Sigma (fun c=>Quotient (relSetoid (r c))) := by
  let f : Quotient (relSetoid (inComponent r)) → Sigma (fun c=>Quotient (relSetoid (r c))) :=
    Quotient.lift (label r) (fun x y h=>(component_path_iff r x y).mp h)
  apply Equiv.ofBijective f
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        intro h
        exact Quotient.sound ((component_path_iff r a b).mpr h)
  · rintro ⟨c,q⟩
    induction q using Quotient.inductionOn with
    | h z => exact ⟨Quotient.mk _ ⟨c,z⟩,rfl⟩

variable [Fintype C] [∀ c,Fintype (X c)] [∀ c,Fintype (E c)]
variable {R : Type*} [CommSemiring R] [DecidableEq C] [∀ c,DecidableEq (E c)]

end RibbonComponents

section MarkedPorts

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary

variable {X E : Type*}

def portIndex {G A : X→X} (C : AlternatingFlagChart G A) (x : X) : D C.n :=
  (C.chart.symm x).1

private theorem portIndex_iff {G A : X→X} (C : AlternatingFlagChart G A)
    (hA : Function.Involutive A) (x y:X) :
    portIndex C x = portIndex C y ↔ x=y ∨ A x=y := by
  obtain ⟨⟨i,s⟩,rfl⟩ := C.chart.surjective x
  obtain ⟨⟨j,t⟩,rfl⟩ := C.chart.surjective y
  have h (i:D C.n) : A (C.chart (outFlag i)) = C.chart (inFlag i) := by
    rw [← C.base i,hA]
  constructor
  · intro he
    simp only [portIndex,Equiv.symm_apply_apply] at he
    subst j
    cases s <;> cases t
    · exact .inl rfl
    · exact .inr (C.base i)
    · exact .inr (h i)
    · exact .inl rfl
  · rintro (he|he)
    · simp only [portIndex,Equiv.symm_apply_apply]
      exact congrArg Prod.fst (C.chart.injective he)
    · cases s with
      | false =>
        change A (C.chart (inFlag i))=C.chart (j,t) at he
        rw [C.base] at he
        simp only [portIndex,Equiv.symm_apply_apply]
        exact congrArg Prod.fst (C.chart.injective he)
      | true =>
        change A (C.chart (outFlag i))=C.chart (j,t) at he
        rw [h] at he
        simp only [portIndex,Equiv.symm_apply_apply]
        exact congrArg Prod.fst (C.chart.injective he)

structure OrderedPortLabels (E : Type*) (n : ℕ) where
  a : E→D n
  b : E→D n
  a_inj : Function.Injective a
  b_inj : Function.Injective b
  separate : ∀ e f, a e≠b f
  ordered : ∀ e,(a e).val < (b e).val

/-- Two distinct marked matching ports per edge can be canonically
ordered, with no external endpoint-label table. -/
noncomputable def order_marked_ports {G A : X→X} (C : AlternatingFlagChart G A)
    (hA : Function.Involutive A) (p : E×Bool→X)
    (hdis : ∀ f g : E×Bool, p f=p g ∨ A (p f)=p g → f=g) :
    OrderedPortLabels E C.n := by
  let q (x:E×Bool) := portIndex C (p x)
  have hq : Function.Injective q := fun f g h=>hdis f g ((portIndex_iff C hA _ _).mp h)
  let flip (e:E) : Bool := decide (q (e,true) < q (e,false))
  let a (e:E) := q (e,flip e)
  let b (e:E) := q (e,!(flip e))
  refine ⟨a,b,?_,?_,?_,?_⟩
  · intro e f h
    exact congrArg Prod.fst (hq h)
  · intro e f h
    exact congrArg Prod.fst (hq h)
  · intro e f h
    have he : (e,flip e)=(f,!(flip f)) := hq h
    have hef : e=f := congrArg Prod.fst he
    subst f
    have hc : flip e = !(flip e) := congrArg Prod.snd he
    cases hh : flip e <;> simp [hh] at hc
  · intro e
    change a e < b e
    by_cases h : q (e,true) < q (e,false)
    · simpa [a,b,flip,h] using h
    · have hne : q (e,false)≠q (e,true) := by
        intro he
        have hx := congrArg Prod.snd (hq he)
        contradiction
      have hl := lt_of_le_of_ne (le_of_not_gt h) hne
      simpa [a,b,flip,h] using hl

private theorem signed_chart_of_local_switch [Fintype X] [DecidableEq X] {G A : X→X} (C : AlternatingFlagChart G A)
    (i j : D C.n) (b : X→X) (hb : Function.Involutive b)
    (h1 : portIndex C (b (C.chart (inFlag i)))=j)
    (h2 : portIndex C (b (C.chart (outFlag i)))=j) :
    ∃ t : Bool,
      b (C.chart (inFlag i))=C.chart (if t then inFlag j else outFlag j) ∧
      b (C.chart (outFlag i))=C.chart (if t then outFlag j else inFlag j) := by
  have port (z:X) (hz:portIndex C z=j) :
      z=C.chart (inFlag j) ∨ z=C.chart (outFlag j) := by
    obtain ⟨⟨k,s⟩,rfl⟩ := C.chart.surjective z
    simp only [portIndex,Equiv.symm_apply_apply] at hz
    subst k
    cases s
    · exact .inl rfl
    · exact .inr rfl
  exact signed_alternative_from_chart G A C i j b hb (port _ h1) (port _ h2)

end MarkedPorts

section MarkedSwitchAction

open Relation

variable {E X : Type*} [DecidableEq X]

abbrev BandFlag (E : Type*) := E × Bool × Bool

/-- Indicator false pairs the two flags at the same port; true changes
ports with the prescribed twist. Both choices are literal involutions. -/
def bandCode (τ s : Bool) (q : Bool×Bool) : Bool×Bool :=
  if s then (!q.1,q.2 ^^ τ) else (q.1,!q.2)

private theorem bandCode_inv (τ s : Bool) : Function.Involutive (bandCode τ s) := by
  rintro ⟨a,b⟩
  cases τ <;> cases s <;> cases a <;> cases b <;> rfl

private theorem bandCode_free (τ s : Bool) (q : Bool×Bool) : bandCode τ s q ≠ q := by
  rcases q with ⟨a,b⟩
  cases τ <;> cases s <;> cases a <;> cases b <;> decide
/-- The action of a binary assignment on globally disjoint marked flags.
The gap is independent and the unmarked cap involution is unaltered. -/
noncomputable def markedAction (A : X→X) (mark : BandFlag E→X)
    (t s : E→Bool) (x:X) : X := by
  classical
  exact if h : ∃ q, mark q=x then
    let q:=Classical.choose h
    mark (q.1,bandCode (t q.1) (s q.1) q.2)
  else A x

private theorem markedAction_apply_mark (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) (q:BandFlag E) :
    markedAction A mark t s (mark q) = mark (q.1,bandCode (t q.1) (s q.1) q.2) := by
  classical
  unfold markedAction
  split
  · rename_i h
    have hh := hm (Classical.choose_spec h)
    rw [hh]
  · rename_i h
    exact (h ⟨q,rfl⟩).elim

private theorem markedAction_apply_unmarked (A : X→X) (mark : BandFlag E→X)
    (t s : E→Bool) (x:X) (hx : ¬∃ q,mark q=x) :
    markedAction A mark t s x=A x := by
  classical
  unfold markedAction
  exact dif_neg hx

/-- Any state is an honest matching, including simultaneous switches on
all bands, without any order dependence. -/
private theorem markedAction_match (A : X→X) (mark : BandFlag E→X)
    (hA : Function.Involutive A) (hAf : ∀ x,A x≠x) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) :
    Function.Involutive (markedAction A mark t s) ∧
      ∀ x, markedAction A mark t s x≠x := by
  classical
  constructor
  · intro x
    by_cases he : ∃ q,mark q=x
    · obtain ⟨q,rfl⟩ := he
      rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
      exact congrArg (fun v=>mark (q.1,v)) (bandCode_inv (t q.1) (s q.1) q.2)
    · have ha : ¬∃ q, mark q=A x := by
        rintro ⟨q,hq⟩
        apply he
        use (q.1,bandCode false false q.2)
        rw [← h0 q,hq,hA]
      rw [markedAction_apply_unmarked _ _ _ _ _ he,markedAction_apply_unmarked _ _ _ _ _ ha,hA]
  · intro x
    by_cases he : ∃ q,mark q=x
    · obtain ⟨q,rfl⟩ := he
      rw [markedAction_apply_mark _ _ hm]
      intro h
      exact bandCode_free (t q.1) (s q.1) q.2 (congrArg Prod.snd (hm h))
    · rw [markedAction_apply_unmarked _ _ _ _ _ he]
      exact hAf x

/-- Post-dual representatives of the two ports of a band. If the base
choice crosses ports, use the two flags on its original left port. -/
def statePortRep (s : E→Bool) (x : E×Bool) : BandFlag E :=
  if s x.1 then (x.1,false,x.2) else (x.1,x.2,false)

private theorem statePortRep_inj (s : E→Bool) : Function.Injective (statePortRep s) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hh : e=f := by
    have hx := congrArg Prod.fst h
    simpa [statePortRep,apply_ite] using hx
  subst f
  by_cases hs : s e=true
  · simpa [statePortRep,hs] using h
  · simpa [statePortRep,hs] using h

/-- These chosen representations are globally distinct even as matching
ports, including edges that became loops after taking the forest. -/
private theorem statePortRep_disjoint (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) :
    ∀ f g : E×Bool,
      mark (statePortRep s f) = mark (statePortRep s g) ∨
      markedAction A mark t s (mark (statePortRep s f)) = mark (statePortRep s g) → f=g := by
  rintro ⟨e,b⟩ ⟨f,c⟩ (h|h)
  · exact statePortRep_inj s (hm h)
  · rw [markedAction_apply_mark _ _ hm] at h
    have h := hm h
    have he : e=f := by
      have hh := congrArg Prod.fst h
      simpa [statePortRep,apply_ite] using hh
    subst f
    cases ht : t e <;> cases hs : s e <;> cases b <;> cases c <;>
      simp [statePortRep,ht,hs,bandCode] at h

end MarkedSwitchAction

section MarkedForest

open Relation
variable {E X : Type*} [Fintype X] [DecidableEq X] [DecidableEq E]

def bandEnds (mark : BandFlag E→X) (e:E) : X×X :=
  (mark (e,false,false),mark (e,true,false))

private theorem marked_on_onestate (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) (e:E) (a b : Bool) :
    markedAction A mark t (Function.update s e true) (mark (e,a,b)) =
      mark (e,!a,b ^^ t e) := by
  rw [markedAction_apply_mark _ _ hm]
  simp [bandCode]

private theorem marked_off_onestate (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) (e:E) (h:s e=false) (a b : Bool) :
    markedAction A mark t s (mark (e,a,b)) = mark (e,a,!b) := by
  rw [markedAction_apply_mark _ _ hm]
  simp [bandCode,h]

/-- Switching one not-yet-selected genuine band merges exactly the
classes specified by its physical endpoint flags. -/
private theorem marked_band_join (G A : X→X) (hG : Function.Involutive G)
    (hGf : ∀ x,G x≠x) (hA : Function.Involutive A) (hAf : ∀ x,A x≠x)
    (mark : BandFlag E→X) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) (e:E) (he:s e=false)
    (hsep : ¬wholeConn G (markedAction A mark t s) (bandEnds mark e).1 (bandEnds mark e).2)
    (x y:X) :
    wholeConn G (markedAction A mark t (Function.update s e true)) x y ↔
      addedJoin (wholeConn G (markedAction A mark t s)) (bandEnds mark e).1 (bandEnds mark e).2 x y := by
  let a := (bandEnds mark e).1
  let b := (bandEnds mark e).2
  let L := markedAction A mark t s
  let M := markedAction A mark t (Function.update s e true)
  have hLa : L a=mark (e,false,true) := marked_off_onestate _ _ hm _ _ _ he false false
  have hLb : L b=mark (e,true,true) := marked_off_onestate _ _ hm _ _ _ he true false
  have hL := markedAction_match A mark hA hAf hm h0 t s
  apply match_switch_join G L M hG hL.1 hGf hL.2 a b hsep _ _ _ x y
  · intro z hz
    obtain ⟨q,rfl⟩ | hu := em (∃ q,mark q=z)
    · rcases q with ⟨f,i,j⟩
      have hfe : f≠e := by
        intro h
        subst f
        apply hz
        rw [hLa,hLb]
        cases i <;> cases j
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inr (.inr rfl))
      dsimp [L,M]
      rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
      simp [Function.update_of_ne hfe]
    · dsimp [L,M]
      rw [markedAction_apply_unmarked _ _ _ _ _ hu, markedAction_apply_unmarked _ _ _ _ _ hu]
  · intro z hz
    rw [hLa] at hz
    rw [hLb]
    rcases hz with rfl|rfl
    · change M (mark (e,false,false)) = b ∨ M (mark (e,false,false)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inl rfl
      · exact .inr rfl
    · change M (mark (e,false,true)) = b ∨ M (mark (e,false,true)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inr rfl
      · exact .inl rfl
  · intro z hz
    rw [hLb] at hz
    rw [hLa]
    rcases hz with rfl|rfl
    · change M (mark (e,true,false)) = a ∨ M (mark (e,true,false)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inl rfl
      · exact .inr rfl
    · change M (mark (e,true,true)) = a ∨ M (mark (e,true,true)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inr rfl
      · exact .inl rfl

/-- Greedy forest realization on the actual binary state function of
the disjoint marked ribbon, not merely on an existential permutation. -/
private theorem marked_forest_state (G A : X→X) (hG : Function.Involutive G)
    (hGf : ∀ x,G x≠x) (hA : Function.Involutive A) (hAf : ∀ x,A x≠x)
    (mark : BandFlag E→X) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) (l : List E) (hn:l.Nodup) (hf:∀ e∈l,s e=false) :
    ∃ s' : E→Bool, (∀ e, e∉l → s' e = s e) ∧
      ∀ x y, wholeConn G (markedAction A mark t s') x y ↔
        graphJoin (wholeConn G (markedAction A mark t s)) (l.map (bandEnds mark)) x y := by
  classical
  induction l generalizing s with
  | nil =>
    refine ⟨s,fun _ _=>rfl,fun x y=>⟨fun h=>.rel _ _ (.inl h),?_⟩⟩
    apply eqvGen_transfer _ (eqvGen_is_equivalence _)
    intro i j h
    exact h.elim id (fun hh=>(List.not_mem_nil hh).elim)
  | cons e l ih =>
    let R := wholeConn G (markedAction A mark t s)
    let a := (bandEnds mark e).1
    let b := (bandEnds mark e).2
    have he := (List.nodup_cons.mp hn).1
    have hn' := (List.nodup_cons.mp hn).2
    have hrest : ∀ f∈l,s f=false := fun f h=>hf f (List.mem_cons_of_mem _ h)
    have hg (x y:X) := graphJoin_cons R a b (l.map (bandEnds mark)) x y
    by_cases hc : R a b
    · obtain ⟨s',hs',hw⟩ := ih s hn' hrest
      let eqR : Equivalence R := eqvGen_is_equivalence _
      have hsame (i j:X) : R i j ↔ addedJoin R a b i j := by
        refine ⟨fun h=>.rel _ _ (.inl h),?_⟩
        apply eqvGen_transfer _ eqR
        intro i j h
        rcases h with h|⟨rfl,rfl⟩
        · exact h
        · exact hc
      exact ⟨s',fun f h=>hs' f (fun hm=>h (List.mem_cons_of_mem _ hm)),fun x y=>
        (hw x y).trans ((graphJoin_congr hsame (l.map (bandEnds mark)) x y).trans (hg x y))⟩
    · let S := Function.update s e true
      have hrest' (f:E) (hfl:f∈l) : S f=false := by
        have hne : f≠e := fun h=>he (h ▸ hfl)
        simp [S,Function.update_of_ne hne,hrest f hfl]
      obtain ⟨s',hs',hw⟩ := ih S hn' hrest'
      have hstep (i j:X) : wholeConn G (markedAction A mark t S) i j ↔ addedJoin R a b i j :=
        marked_band_join G A hG hGf hA hAf mark hm h0 t s e (hf e (List.mem_cons_self ..)) hc i j
      refine ⟨s',?_,fun x y=>(hw x y).trans
        ((graphJoin_congr hstep (l.map (bandEnds mark)) x y).trans (hg x y))⟩
      intro f h
      have hne : f≠e := fun he=>h (he ▸ List.mem_cons_self ..)
      have hnmem : f∉l := fun hm=>h (List.mem_cons_of_mem _ hm)
      simp [hs' f hnmem,S,Function.update_of_ne hne]

end MarkedForest

section MarkedBouquet

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open Relation

variable {E X : Type*} [Fintype X] [DecidableEq X]

def postSlot (t s : Bool) (q:Bool×Bool) : Bool :=
  if s then q.2 ^^ (q.1 && t) else q.1
private theorem postSlot_opposite (t s : Bool) (q:Bool×Bool) :
    postSlot t s (bandCode t (!s) q) = !(postSlot t s q) := by
  rcases q with ⟨a,b⟩
  cases t <;> cases s <;> cases a <;> cases b <;> rfl

private theorem mark_index_from_slot (G A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool)
    (C : AlternatingFlagChart G (markedAction A mark t s))
    (hA : Function.Involutive (markedAction A mark t s))
    (e:E) (q:Bool×Bool) :
    portIndex C (mark (e,q)) =
      portIndex C (mark (statePortRep s (e,postSlot (t e) (s e) q))) := by
  apply (portIndex_iff C hA _ _).mpr
  rw [markedAction_apply_mark _ _ hm]
  rcases q with ⟨a,b⟩
  cases hs : s e <;> cases ht : t e <;> cases a <;> cases b <;>
    simp [bandCode,postSlot,statePortRep,hs,ht]

private theorem order_marked_ports_witness {G A : X→X} (C : AlternatingFlagChart G A)
    (hA : Function.Involutive A) (p : E×Bool→X)
    (hdis : ∀ f g : E×Bool, p f=p g ∨ A (p f)=p g → f=g) :
    ∀ e, ∃ k : Bool,
       (order_marked_ports C hA p hdis).a e = portIndex C (p (e,k)) ∧
       (order_marked_ports C hA p hdis).b e = portIndex C (p (e,!k)) := by
  intro e
  exact ⟨decide (portIndex C (p (e,true)) < portIndex C (p (e,false))),rfl,rfl⟩

structure SignedMarkedChart (G A : X→X) (alt : X→X) (E : Type*) (support : E→X→Prop) where
  C : AlternatingFlagChart G A
  ports : OrderedPortLabels E C.n
  twist : E → Bool
  membership : ∀ e x, support e x ↔ portIndex C x = ports.a e ∨ portIndex C x = ports.b e
  in_alternative : ∀ e,
    alt (C.chart (inFlag (ports.a e))) =
    C.chart (if twist e then inFlag (ports.b e) else outFlag (ports.b e))
  out_alternative : ∀ e,
    alt (C.chart (outFlag (ports.a e))) =
    C.chart (if twist e then outFlag (ports.b e) else inFlag (ports.b e))

/-- Actual toggling of each band is a canonical signed pairing in the
constructed chart, regardless of original orientations or the forest
edges that were selected. -/
noncomputable def canonical_marked_signed_chart
    (G A : X→X) (hA : Function.Involutive A) (hAf : ∀ x,A x≠x)
    (mark : BandFlag E→X) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) (C : AlternatingFlagChart G (markedAction A mark t s)) :
    SignedMarkedChart G (markedAction A mark t s) (markedAction A mark t (fun e=>!(s e))) E (fun e x=>∃ q:Bool×Bool, x=mark (e,q)) := by
  classical
  let B := markedAction A mark t s
  let B' := markedAction A mark t (fun e=>!(s e))
  have hi : Function.Involutive B := (markedAction_match A mark hA hAf hm h0 t s).1
  have hi' : Function.Involutive B' := (markedAction_match A mark hA hAf hm h0 t _).1
  let p : E×Bool→X := fun f=>mark (statePortRep s f)
  let D := order_marked_ports C hi p (statePortRep_disjoint A mark hm t s)
  have exists_of_port (e:E) (k:Bool) (z:X)
      (hn : portIndex C (p (e,k)) = portIndex C z) :
      ∃ q : Bool×Bool, z=mark (e,q) := by
    have hh := (portIndex_iff C hi _ _).mp hn
    change p (e,k)=z ∨ B (p (e,k))=z at hh
    rcases hh with hh|hh
    · use (statePortRep s (e,k)).2
      have he : (statePortRep s (e,k)).1=e := by simp [statePortRep,apply_ite]
      have hp : p (e,k)=mark (e,(statePortRep s (e,k)).2) := by
        dsimp [p]
        congr 1
        exact Prod.ext he rfl
      exact hh.symm.trans hp
    · dsimp [p,B] at hh
      rw [markedAction_apply_mark _ _ hm] at hh
      have he : (statePortRep s (e,k)).1=e := by simp [statePortRep,apply_ite]
      use bandCode (t (statePortRep s (e,k)).1) (s (statePortRep s (e,k)).1) (statePortRep s (e,k)).2
      exact hh.symm.trans (congrArg mark (Prod.ext he rfl))
  have membership (e:E) (z:X) :
      (∃ q:Bool×Bool,z=mark (e,q)) ↔ portIndex C z=D.a e ∨ portIndex C z=D.b e := by
    obtain ⟨k,ha,hb⟩ := order_marked_ports_witness C hi p (statePortRep_disjoint A mark hm t s) e
    change D.a e = _ at ha
    change D.b e = _ at hb
    rw [ha,hb]
    constructor
    · rintro ⟨q,rfl⟩
      have hq := mark_index_from_slot G A mark hm t s C hi e q
      cases hk : k <;> cases hh : postSlot (t e) (s e) q <;>
        simp only [hh,hk,Bool.not_false,Bool.not_true] at hq ⊢
      · exact .inl hq
      · exact .inr hq
      · exact .inr hq
      · exact .inl hq
    · rintro (hh|hh)
      · exact exists_of_port e k z hh.symm
      · exact exists_of_port e (!k) z hh.symm
  have hiAlt (e:E) (j:Bool) : portIndex C (B' (C.chart (D.a e,j))) = D.b e := by
    obtain ⟨k,hka,hkb⟩ := order_marked_ports_witness C hi p (statePortRep_disjoint A mark hm t s) e
    change D.a e = _ at hka
    change D.b e = _ at hkb
    let z := C.chart (D.a e,j)
    have hz : portIndex C (p (e,k)) = portIndex C z := by
      rw [← hka]
      simp [z,portIndex]
    have hmz := exists_of_port e k z hz
    obtain ⟨q,hq⟩ := hmz
    let u := postSlot (t e) (s e) q
    have hu : u=k := by
      have h1 : portIndex C (p (e,u)) = portIndex C (p (e,k)) := by
        change portIndex C (mark (statePortRep s (e,u))) = _
        rw [← mark_index_from_slot G A mark hm t s C hi e q,← hq]
        exact hz.symm
      have he := statePortRep_disjoint A mark hm t s (e,u) (e,k)
        ((portIndex_iff C hi _ _).mp h1)
      exact congrArg Prod.snd he
    change portIndex C (B' z) = D.b e
    rw [hq, show B' (mark (e,q)) = mark (e,bandCode (t e) (!(s e)) q)
      from markedAction_apply_mark _ _ hm _ _ (e,q)]
    rw [mark_index_from_slot G A mark hm t s C hi,postSlot_opposite]
    change portIndex C (p (e,!u))=D.b e
    rw [hu,← hkb]
  have H (e:E) := signed_chart_of_local_switch C (D.a e) (D.b e) B' hi'
    (hiAlt e false) (hiAlt e true)
  exact ⟨C,D,fun e=>Classical.choose (H e),membership,fun e=>(Classical.choose_spec (H e)).1,
    fun e=>(Classical.choose_spec (H e)).2⟩

end MarkedBouquet

section FlagMatchingEqv

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open Relation

variable {E X : Type*} [Fintype X] [DecidableEq X]

private theorem cyclicNext_surj (n:ℕ) : Function.Surjective (@cyclicNext n) := by
  intro i
  by_cases h : i.val=0
  · refine ⟨⟨n,Nat.lt_succ_self _⟩,Fin.ext ?_⟩
    change (n+1)%(n+1)=i.val
    simp [h]
  · refine ⟨⟨i.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,Fin.ext ?_⟩
    change (i.val-1+1)%(n+1)=i.val
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h),Nat.mod_eq_of_lt i.isLt]

private theorem map_eqv {Y Z : Type*} {R : Y→Y→Prop} {S : Z→Z→Prop} (f : Y→Z)
    (h : ∀ x y,R x y→EqvGen S (f x) (f y)) {x y:Y} (hxy:EqvGen R x y) :
    EqvGen S (f x) (f y) := by
  induction hxy with
  | rel x y hr => exact h x y hr
  | refl x => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Direct exact action-to-boundary equivalence; every cap, gap or
physical switched band is carried through the actual extraction chart. -/
private theorem matching_is_literal_boundary (G B F : X→X) (hG : Function.Involutive G)
    (hF : Function.Involutive F) (C : AlternatingFlagChart G B)
    (a b : E→D C.n) (t:E→Bool)
    (cap : ∀ i, (∀ e,a e≠i) → (∀ e,b e≠i) → F (C.chart (inFlag i))=C.chart (outFlag i))
    (hI : ∀ e,F (C.chart (inFlag (a e)))=C.chart (if t e then inFlag (b e) else outFlag (b e)))
    (hO : ∀ e,F (C.chart (outFlag (a e)))=C.chart (if t e then outFlag (b e) else inFlag (b e)))
    (x y : Flag C.n) :
    wholeConn G F (C.chart x) (C.chart y) ↔ EqvGen (FlagLink a b t) x y := by
  have arc (i:D C.n) : EqvGen (FlagLink a b t) (outFlag i) (inFlag (cyclicNext i)) :=
    .rel _ _ (.arc _)
  have lI (e:E) : EqvGen (FlagLink a b t) (inFlag (a e)) (if t e then inFlag (b e) else outFlag (b e)) := by
    cases h:t e
    · exact .symm _ _ (.rel _ _ (.crossB _ h))
    · exact .rel _ _ (.twistIn _ h)
  have lO (e:E) : EqvGen (FlagLink a b t) (outFlag (a e)) (if t e then outFlag (b e) else inFlag (b e)) := by
    cases h:t e
    · exact .rel _ _ (.crossA _ h)
    · exact .rel _ _ (.twistOut _ h)
  have hg (x:Flag C.n) : EqvGen (FlagLink a b t) x (C.chart.symm (G (C.chart x))) := by
    rcases x with ⟨i,c⟩
    cases c
    · obtain ⟨j,hj⟩ := cyclicNext_surj C.n i
      have he := congrArg G (C.gap j)
      rw [hG,hj] at he
      change EqvGen (FlagLink a b t) (inFlag i) (C.chart.symm (G (C.chart (inFlag i))))
      rw [← he,Equiv.symm_apply_apply,← hj]
      exact .symm _ _ (arc _)
    · change EqvGen (FlagLink a b t) (outFlag i) (C.chart.symm (G (C.chart (outFlag i))))
      rw [C.gap,Equiv.symm_apply_apply]
      exact arc _
  have hf (x:Flag C.n) : EqvGen (FlagLink a b t) x (C.chart.symm (F (C.chart x))) := by
    rcases x with ⟨i,c⟩
    by_cases hL : ∃ e, a e=i
    · obtain ⟨e,rfl⟩ := hL
      cases c
      · change EqvGen (FlagLink a b t) (inFlag (a e)) (C.chart.symm (F (C.chart (inFlag (a e)))))
        rw [hI,Equiv.symm_apply_apply]
        exact lI _
      · change EqvGen (FlagLink a b t) (outFlag (a e)) (C.chart.symm (F (C.chart (outFlag (a e)))))
        rw [hO,Equiv.symm_apply_apply]
        exact lO _
    · by_cases hR : ∃ e, b e=i
      · obtain ⟨e,rfl⟩ := hR
        have qI := congrArg F (hI e)
        have qO := congrArg F (hO e)
        rw [hF] at qI qO
        cases ht : t e <;> simp only [ht, Bool.false_eq_true, if_false, if_true] at qI qO
        · cases c
          · change EqvGen (FlagLink a b t) (inFlag (b e)) (C.chart.symm (F (C.chart (inFlag (b e)))))
            rw [← qO,Equiv.symm_apply_apply]
            exact .symm _ _ (.rel _ _ (.crossA _ ht))
          · change EqvGen (FlagLink a b t) (outFlag (b e)) (C.chart.symm (F (C.chart (outFlag (b e)))))
            rw [← qI,Equiv.symm_apply_apply]
            exact .rel _ _ (.crossB _ ht)
        · cases c
          · change EqvGen (FlagLink a b t) (inFlag (b e)) (C.chart.symm (F (C.chart (inFlag (b e)))))
            rw [← qI,Equiv.symm_apply_apply]
            exact .symm _ _ (.rel _ _ (.twistIn _ ht))
          · change EqvGen (FlagLink a b t) (outFlag (b e)) (C.chart.symm (F (C.chart (outFlag (b e)))))
            rw [← qO,Equiv.symm_apply_apply]
            exact .symm _ _ (.rel _ _ (.twistOut _ ht))
      · have hcap := cap i (fun e h=>hL ⟨e,h⟩) (fun e h=>hR ⟨e,h⟩)
        have forward : EqvGen (FlagLink a b t) (outFlag i) (inFlag i) :=
          .rel _ _ (.cap i (fun e h=>hL ⟨e,h⟩) (fun e h=>hR ⟨e,h⟩))
        cases c
        · change EqvGen (FlagLink a b t) (inFlag i) (C.chart.symm (F (C.chart (inFlag i))))
          rw [hcap,Equiv.symm_apply_apply]
          exact .symm _ _ forward
        · have hrev := congrArg F hcap
          rw [hF] at hrev
          change EqvGen (FlagLink a b t) (outFlag i) (C.chart.symm (F (C.chart (outFlag i))))
          rw [← hrev,Equiv.symm_apply_apply]
          exact forward
  constructor
  · intro h
    have hh := map_eqv C.chart.symm
      (R:=matchStep G F (fun _=>False)) (S:=FlagLink a b t) (fun i j hstep=>by
        obtain ⟨x,rfl⟩ := C.chart.surjective i
        rcases hstep with rfl|⟨_,rfl⟩
        · simpa using hg x
        · simpa using hf x) h
    simpa using hh
  · apply map_eqv C.chart
    intro i j h
    cases h with
    | arc i => exact .rel _ _ (.inl (C.gap i).symm)
    | cap i ha hb => exact .symm _ _ (.rel _ _ (.inr ⟨id,(cap i ha hb).symm⟩))
    | crossA e ht =>
      exact .rel _ _ (.inr ⟨id,by simpa [ht] using (hO e).symm⟩)
    | crossB e ht =>
      exact .symm _ _ (.rel _ _ (.inr ⟨id,by simpa [ht] using (hI e).symm⟩))
    | twistIn e ht =>
      exact .rel _ _ (.inr ⟨id,by simpa [ht] using (hI e).symm⟩)
    | twistOut e ht =>
      exact .rel _ _ (.inr ⟨id,by simpa [ht] using (hO e).symm⟩)

end FlagMatchingEqv

section MarkedMoments

open Finset Relation
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

variable {E X : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

def matchSetoid (G B:X→X) : Setoid X :=
  ⟨wholeConn G B,eqvGen_is_equivalence _⟩

noncomputable def markedCircleCount (G A:X→X) (mark:BandFlag E→X) (t s:E→Bool) : ℕ :=
  Nat.card (Quotient (matchSetoid G (markedAction A mark t s)))
private theorem marked_xor_action_inactive (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t τ s : E→Bool) (e:E) (h:s e=false) (q:Bool×Bool) :
    markedAction A mark t (switch τ s) (mark (e,q)) =
      markedAction A mark t τ (mark (e,q)) := by
  rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
  cases hτ : τ e <;> simp [switch,h,hτ]

private theorem marked_xor_action_active (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t τ s : E→Bool) (e:E) (h:s e=true) (q:Bool×Bool) :
    markedAction A mark t (switch τ s) (mark (e,q)) =
      markedAction A mark t (fun a=>!(τ a)) (mark (e,q)) := by
  rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
  cases hτ : τ e <;> simp [switch,h,hτ]

/-- Actual boundary counts at each state before and after the selected
forest, with the exact input weights subsequently toggled by XOR. -/
private theorem physical_chart_counts (G A:X→X) (hG:Function.Involutive G) (hA:Function.Involutive A)
    (hAf:∀ x,A x≠x) (mark:BandFlag E→X) (hm:Function.Injective mark)
    (h0:∀ q,A (mark q)=mark (q.1,bandCode false false q.2)) (t τ s:E→Bool)
    (C : SignedMarkedChart G (markedAction A mark t τ)
      (markedAction A mark t (fun e=>!(τ e))) E (fun e x=>∃ q:Bool×Bool,x=mark (e,q))) :
    markedCircleCount G A mark t (switch τ s) =
      signedBouquetCircleCount C.ports.a C.ports.b C.twist (selected s) := by
  let P := C.C
  let a := C.ports.a
  let b := C.ports.b
  let F := markedAction A mark t (switch τ s)
  let B := markedAction A mark t τ
  let Calt := markedAction A mark t (fun e=>!(τ e))
  have hF : Function.Involutive F := (markedAction_match A mark hA hAf hm h0 t _).1
  have cap (i:D P.n) (ha:∀ e:selected s,a e≠i) (hb:∀ e:selected s,b e≠i) :
      F (P.chart (inFlag i)) = P.chart (outFlag i) := by
    let x := P.chart (inFlag i)
    have he : portIndex P x=i := by simp [x,portIndex,inFlag]
    have hFB : F x=B x := by
      by_cases hx : ∃ q,mark q=x
      · obtain ⟨⟨e,q⟩,hqx⟩ := hx
        have hmem := (C.membership e x).mp ⟨q,hqx.symm⟩
        change portIndex P x=a e ∨ portIndex P x=b e at hmem
        rw [he] at hmem
        have hstate : s e=false := by
          cases hs : s e
          · rfl
          · have eS : e∈selected s := (mem_selected_iff s e).mpr hs
            exact hmem.elim (fun h=>(ha ⟨e,eS⟩ h.symm).elim) (fun h=>(hb ⟨e,eS⟩ h.symm).elim)
        rw [← hqx]
        exact marked_xor_action_inactive A mark hm t τ s e hstate q
      · exact (markedAction_apply_unmarked _ _ _ _ _ hx).trans (markedAction_apply_unmarked _ _ _ _ _ hx).symm
    exact hFB.trans (P.base i)
  have switchAt (e : selected s) (j:Bool) : F (P.chart (a e,j))=Calt (P.chart (a e,j)) := by
    let x := P.chart (a e,j)
    have he : portIndex P x=a e := by simp [x,portIndex]
    obtain ⟨q,hq⟩ := (C.membership (e:E) x).mpr (.inl he)
    change F x=Calt x
    rw [hq]
    exact marked_xor_action_active A mark hm t τ s e ((mem_selected_iff s e).mp e.prop) q
  have hI (e:selected s) : F (P.chart (inFlag (a e))) =
      P.chart (if C.twist e then inFlag (b e) else outFlag (b e)) :=
    (switchAt e false).trans (C.in_alternative e)
  have hO (e:selected s) : F (P.chart (outFlag (a e))) =
      P.chart (if C.twist e then outFlag (b e) else inFlag (b e)) :=
    (switchAt e true).trans (C.out_alternative e)
  unfold markedCircleCount signedBouquetCircleCount
  symm
  apply Nat.card_congr
  exact Quotient.congr P.chart (fun x y=>(matching_is_literal_boundary G B F hG hF P
    (fun i:selected s=>a i) (fun i:selected s=>b i) (fun i:selected s=>C.twist i) cap hI hO x y).symm)

end MarkedMoments

section MarkedComponents

open Relation Finset
open scoped BigOperators

variable {J : Type*} {X E : J→Type*}
  [Fintype J] [DecidableEq J] [∀ j,Fintype (X j)] [∀ j,DecidableEq (X j)]
  [∀ j,Fintype (E j)] [∀ j,DecidableEq (E j)]

def sigmaAction (f : ∀ j, X j→X j) (x:Sigma X) : Sigma X :=
  ⟨x.1,f x.1 x.2⟩

def sigmaMark (m : ∀ j, BandFlag (E j)→X j) (q : BandFlag (Sigma E)) : Sigma X :=
  ⟨q.1.1,m q.1.1 (q.1.2,q.2)⟩

private theorem sigmaMark_injective (m : ∀ j, BandFlag (E j)→X j)
    (hm : ∀ j,Function.Injective (m j)) : Function.Injective (sigmaMark m) := by
  intro a b h
  rcases a with ⟨⟨i,e⟩,sa⟩; rcases b with ⟨⟨j,f⟩,sb⟩
  have he : i=j := congrArg Sigma.fst h
  subst j
  have hh : m i (e,sa)=m i (f,sb) := by injection h
  have he := hm _ hh
  cases he
  rfl

private theorem sigma_markedAction_apply (A : ∀ j,X j→X j) (m : ∀ j,BandFlag (E j)→X j)
    (hm : ∀ j,Function.Injective (m j)) (t s : Sigma E→Bool) (j:J) (x:X j) :
    markedAction (sigmaAction A) (sigmaMark m) t s ⟨j,x⟩ =
      ⟨j,markedAction (A j) (m j) (fun e=>t ⟨j,e⟩) (fun e=>s ⟨j,e⟩) x⟩ := by
  by_cases he : ∃ q,m j q=x
  · obtain ⟨⟨e,q⟩,rfl⟩ := he
    change markedAction (sigmaAction A) (sigmaMark m) t s (sigmaMark m (⟨j,e⟩,q)) = _
    rw [markedAction_apply_mark _ _ (sigmaMark_injective m hm),markedAction_apply_mark _ _ (hm j)]
    rfl
  · have he' : ¬∃ q,sigmaMark m q = (⟨j,x⟩ : Sigma X) := by
      rintro ⟨⟨⟨i,e⟩,q⟩,h⟩
      have hi : i=j := congrArg Sigma.fst h
      subst i
      apply he
      refine ⟨(e,q),?_⟩
      injection h
    rw [markedAction_apply_unmarked _ _ _ _ _ he',
      markedAction_apply_unmarked _ _ _ _ _ he]
    rfl

private theorem sigma_matchStep (G F : ∀ j, X j→X j) :
    matchStep (sigmaAction G) (sigmaAction F) (fun _=>False) =
      inComponent (fun j=>matchStep (G j) (F j) (fun _=>False)) := by
  funext x y
  apply propext
  constructor
  · rcases x with ⟨j,x⟩
    rintro (rfl|⟨_,rfl⟩)
    · exact .mk _ _ _ (.inl rfl)
    · exact .mk _ _ _ (.inr ⟨id,rfl⟩)
  · intro h
    cases h with
    | mk j x y h =>
      rcases h with rfl|⟨_,rfl⟩
      · exact .inl rfl
      · exact .inr ⟨id,rfl⟩

private theorem markedCircles_disjoint (G A : ∀ j,X j→X j) (m : ∀ j,BandFlag (E j)→X j)
    (hm : ∀ j,Function.Injective (m j)) (t s : Sigma E→Bool) :
    markedCircleCount (sigmaAction G) (sigmaAction A) (sigmaMark m) t s =
      ∑ j, markedCircleCount (G j) (A j) (m j) (fun e=>t ⟨j,e⟩) (fun e=>s ⟨j,e⟩) := by
  classical
  have he : markedAction (sigmaAction A) (sigmaMark m) t s =
      sigmaAction (fun j=>markedAction (A j) (m j) (fun e=>t ⟨j,e⟩) (fun e=>s ⟨j,e⟩)) := by
    funext q
    rcases q with ⟨j,x⟩
    exact sigma_markedAction_apply A m hm t s j x
  unfold markedCircleCount matchSetoid
  rw [he]
  change Nat.card (Quotient (relSetoid (matchStep (sigmaAction G) (sigmaAction _) _))) = _
  rw [sigma_matchStep,Nat.card_congr (quotient_components _),Nat.card_sigma]
  rfl

end MarkedComponents

section ActualComponents

open Finset Relation

section Fibres
variable {Y J : Type*}

abbrev fibre {Y J : Type*} (p : Y → J) (j : J) := {y : Y // p y = j}

noncomputable instance fibreFintype [Fintype Y] (p:Y→J) (j:J) : Fintype (fibre p j) :=
  Fintype.ofFinite _

def fibreEquiv (p : Y → J) : Y ≃ Sigma (fibre p) where
  toFun y := ⟨p y,⟨y,rfl⟩⟩
  invFun y := y.2.val
  left_inv _ := rfl
  right_inv := by rintro ⟨_,⟨y,rfl⟩⟩; rfl

def fibreAction (p:Y→J) (F:Y→Y) (hF:∀ y,p (F y)=p y) (j:J) (x:fibre p j) : fibre p j :=
  ⟨F x.val,(hF _).trans x.prop⟩

private theorem lift_equivalence {Y Z : Type*} {R : Y→Y→Prop} {S : Z→Z→Prop}
    (f:Y→Z) (h:∀ x y,R x y→EqvGen S (f x) (f y)) {x y:Y} (H:EqvGen R x y) :
    EqvGen S (f x) (f y) := by
  induction H with
  | rel x y hh => exact h x y hh
  | refl x => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

private theorem path_label (p:Y→J) {R:Y→Y→Prop}
    (hR:∀ x y,R x y → p x=p y) {x y:Y} (h:EqvGen R x y) : p x=p y := by
  induction h with
  | rel x y h => exact hR x y h
  | refl x => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem path_restrict (p:Y→J) (R:Y→Y→Prop)
    (hR:∀ x y,R x y → p x=p y) {x y:Y} (h:EqvGen R x y) :
    ∀ (j:J) (hx:p x=j) (hy:p y=j),
      EqvGen (fun a b:fibre p j=>R a.val b.val) ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction h with
  | rel x y h => intro j hx hy; exact .rel _ _ h
  | refl x => intro j hx hy; exact .refl _
  | symm x y h ih => intro j hx hy; exact .symm _ _ (ih _ hy hx)
  | trans x y z h₁ h₂ ih₁ ih₂ =>
    intro j hx hz
    have h' : p x=p y := path_label p hR h₁
    have hy : p y=j := h'.symm.trans hx
    exact .trans _ _ _ (ih₁ j hx hy) (ih₂ j hy hz)

private theorem match_naturality {Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (e:Y≃Z) (G A:Y→Y) (G' A':Z→Z)
    (hg:∀ x,e (G x)=G' (e x)) (ha:∀ x,e (A x)=A' (e x)) (x y:Y) :
    wholeConn G A x y ↔ wholeConn G' A' (e x) (e y) := by
  constructor
  · apply lift_equivalence e
    intro a b h
    rcases h with rfl|⟨_,rfl⟩
    · exact .rel _ _ (.inl (hg a))
    · exact .rel _ _ (.inr ⟨id,ha a⟩)
  · intro h
    have Hg (u:Z) : e.symm (G' u)=G (e.symm u) := by
      rw [← (e.apply_symm_apply u),← hg]
      simp
    have Ha (u:Z) : e.symm (A' u)=A (e.symm u) := by
      rw [← (e.apply_symm_apply u),← ha]
      simp
    have h' := lift_equivalence e.symm
      (R:=matchStep G' A' (fun _=>False)) (S:=matchStep G A (fun _=>False))
      (fun a b h=>by
        rcases h with rfl|⟨_,rfl⟩
        · exact .rel _ _ (.inl (Hg a))
        · exact .rel _ _ (.inr ⟨id,Ha a⟩)) h
    change EqvGen (matchStep G A (fun _=>False)) x y
    simpa only [Equiv.symm_apply_apply] using h'

end Fibres

section Literal
variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

def Incidence (G A:X→X) (m:BandFlag E→X) (x y:X) : Prop :=
  matchStep G A (fun _=>False) x y ∨ ∃ e, x=(bandEnds m e).1 ∧ y=(bandEnds m e).2

def componentSetoid (G A:X→X) (m:BandFlag E→X) : Setoid X := relSetoid (Incidence G A m)

abbrev Components (G A:X→X) (m:BandFlag E→X) := Quotient (componentSetoid G A m)
def component (G A:X→X) (m:BandFlag E→X) : X→Components G A m := Quotient.mk _
def edgeComponent (G A:X→X) (m:BandFlag E→X) (e:E) : Components G A m :=
  component G A m (bandEnds m e).1

private theorem comp_eq_step (G A:X→X) (m:BandFlag E→X) {x y:X}
    (h:Incidence G A m x y) : component G A m x=component G A m y :=
  Quotient.sound (.rel _ _ h)

private theorem comp_G (G A:X→X) (m:BandFlag E→X) (x:X) :
    component G A m (G x)=component G A m x :=
  (comp_eq_step G A m (.inl (.inl rfl))).symm

private theorem comp_A (G A:X→X) (m:BandFlag E→X) (x:X) :
    component G A m (A x)=component G A m x :=
  (comp_eq_step G A m (.inl (.inr ⟨id,rfl⟩))).symm

private theorem comp_mark (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2))
    (e:E) (q:Bool×Bool) : component G A m (m (e,q))=edgeComponent G A m e := by
  have hA (b:Bool) : component G A m (m (e,b,true)) = component G A m (m (e,b,false)) := by
    have h := comp_A G A m (m (e,b,false))
    rw [h0] at h
    exact h
  have hB : component G A m (m (e,true,false))=edgeComponent G A m e :=
    (comp_eq_step G A m (.inr ⟨e,rfl,rfl⟩)).symm
  rcases q with ⟨a,b⟩
  cases a <;> cases b
  · rfl
  · exact hA false
  · exact hB
  · exact (hA true).trans hB

def localGap (G A:X→X) (m:BandFlag E→X) :=
  fibreAction (component G A m) G (comp_G G A m)

def localCap (G A:X→X) (m:BandFlag E→X) :=
  fibreAction (component G A m) A (comp_A G A m)

def localMark (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m)
    (q:BandFlag (fibre (edgeComponent G A m) j)) : fibre (component G A m) j :=
  ⟨m (q.1.val,q.2),(comp_mark G A m h0 q.1.val q.2).trans q.1.prop⟩

private theorem localMark_injective (G A:X→X) (m:BandFlag E→X)
    (hm:Function.Injective m) (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2))
    (j:Components G A m) : Function.Injective (localMark G A m h0 j) := by
  rintro ⟨a,p⟩ ⟨b,q⟩ h
  have h := hm (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg (fun x : BandFlag E=>x.1) h))
    (congrArg (fun x : BandFlag E=>x.2) h)

private theorem localGap_involution (G A:X→X) (m:BandFlag E→X) (hG:Function.Involutive G)
    (j:Components G A m) : Function.Involutive (localGap G A m j) :=
  fun x=>Subtype.ext (hG x.val)

private theorem localCap_involution (G A:X→X) (m:BandFlag E→X) (hA:Function.Involutive A)
    (j:Components G A m) : Function.Involutive (localCap G A m j) :=
  fun x=>Subtype.ext (hA x.val)

private theorem localCap_mark (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m)
    (q:BandFlag (fibre (edgeComponent G A m) j)) :
    localCap G A m j (localMark G A m h0 j q)=
      localMark G A m h0 j (q.1,bandCode false false q.2) :=
  Subtype.ext (h0 (q.1.val,q.2))

private theorem local_step (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m)
    (x y:fibre (component G A m) j) (h:Incidence G A m x.val y.val) :
    @graphJoin (fibre (component G A m) j)
      (wholeConn (localGap G A m j) (localCap G A m j))
      ((Finset.univ : Finset (fibre (edgeComponent G A m) j)).toList.map
        (bandEnds (localMark G A m h0 j))) x y := by
  rcases h with h|⟨e,he,hf⟩
  · apply EqvGen.rel
    left
    apply EqvGen.rel
    rcases h with hl|⟨_,hr⟩
    · exact .inl (Subtype.ext hl)
    · exact .inr ⟨id,Subtype.ext hr⟩
  · apply EqvGen.rel
    right
    let e' : fibre (edgeComponent G A m) j := ⟨e,by rw [edgeComponent,← he]; exact x.prop⟩
    apply List.mem_map.mpr
    refine ⟨e',by simp,Prod.ext (Subtype.ext he.symm) (Subtype.ext hf.symm)⟩

private theorem actual_component_connected (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m) :
    ∀ x y:fibre (component G A m) j,
      graphJoin (wholeConn (localGap G A m j) (localCap G A m j))
        ((Finset.univ : Finset (fibre (edgeComponent G A m) j)).toList.map
           (bandEnds (localMark G A m h0 j))) x y := by
  classical
  intro x y
  have h : EqvGen (Incidence G A m) x.val y.val := Quotient.exact (x.prop.trans y.prop.symm)
  apply eqvGen_transfer (local_step G A m h0 j) (eqvGen_is_equivalence _) x y
  exact path_restrict (component G A m) (Incidence G A m)
    (fun _ _ h=>comp_eq_step G A m h) h j x.prop y.prop

private theorem actual_component_nonempty (G A:X→X) (m:BandFlag E→X) (j:Components G A m) :
    Nonempty (fibre (component G A m) j) := by
  induction j using Quotient.inductionOn with
  | h x => exact ⟨⟨x,rfl⟩⟩


noncomputable instance componentFintype (G A:X→X) (m:BandFlag E→X) : Fintype (Components G A m) := by
  classical
  exact Fintype.ofSurjective (component G A m) (fun j => by
    induction j using Quotient.inductionOn with
    | h a => exact ⟨a,rfl⟩)

private theorem fibre_mark_transport (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (q:BandFlag E) :
    fibreEquiv (component G A m) (m q) =
    sigmaMark (localMark G A m h0) (fibreEquiv (edgeComponent G A m) q.1,q.2) := by
  apply (fibreEquiv (component G A m)).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

/-- Boundary circles split over actual quotient fibres for every literal
state, with arbitrary representative ordering and including empty carriers. -/
private theorem actual_circles_components (G A:X→X) (m:BandFlag E→X)
    (hm:Function.Injective m)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (t s:E→Bool) :
    markedCircleCount G A m t s =
      ∑ j : Components G A m,
        markedCircleCount (localGap G A m j) (localCap G A m j)
          (localMark G A m h0 j) (fun e=>t e.val) (fun e=>s e.val) := by
  classical
  let jX := fibreEquiv (component G A m)
  let jE := fibreEquiv (edgeComponent G A m)
  let G' := sigmaAction (localGap G A m)
  let A' := sigmaAction (localCap G A m)
  let m' := sigmaMark (localMark G A m h0)
  let t' := t ∘ jE.symm
  let s' := s ∘ jE.symm
  let B := markedAction A m t s
  let B' := markedAction A' m' t' s'
  have hG (x:X) : jX (G x)=G' (jX x) := by
    apply jX.symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  have hA (x:X) : jX (A x)=A' (jX x) := by
    apply jX.symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  have hB (x:X) : jX (B x)=B' (jX x) := by
    by_cases hx : ∃ q,m q=x
    · obtain ⟨⟨e,q⟩,rfl⟩ := hx
      dsimp only [B,B']
      rw [markedAction_apply_mark _ _ hm,fibre_mark_transport G A m h0,
        fibre_mark_transport G A m h0,
        markedAction_apply_mark _ _ (sigmaMark_injective _ (localMark_injective G A m hm h0))]
      dsimp only [t',s',Function.comp_apply]
      change m' (jE e,bandCode (t e) (s e) q) =
        m' (jE e,bandCode (t (jE.symm (jE e))) (s (jE.symm (jE e))) q)
      rw [Equiv.symm_apply_apply]
    · have hx' : ¬∃ q,m' q=jX x := by
        rintro ⟨⟨e,q⟩,he⟩
        apply hx
        obtain ⟨e,rfl⟩ := jE.surjective e
        apply Exists.intro (e,q)
        apply jX.injective
        exact (fibre_mark_transport G A m h0 (e,q)).trans he
      dsimp only [B,B']
      rw [markedAction_apply_unmarked _ _ _ _ _ hx,
        markedAction_apply_unmarked _ _ _ _ _ hx']
      exact hA x
  have hw : markedCircleCount G A m t s =
      markedCircleCount G' A' m' t' s' := by
    unfold markedCircleCount
    apply Nat.card_congr
    exact Quotient.congr jX (match_naturality jX G B G' B' hG hB)
  rw [hw,markedCircles_disjoint _ _ _ (localMark_injective G A m hm h0)]
  rfl


end Literal

end ActualComponents

section JointColumns

open Finset
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open scoped BigOperators
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

section Joint
variable {J : Type*} [Fintype J] [DecidableEq J] {E V : J→Type*}
  [∀ j,Fintype (E j)] [∀ j,DecidableEq (E j)]
  [∀ j,AddCommGroup (V j)] [∀ j,Module K (V j)] [∀ j,FiniteDimensional K (V j)]

def jointLabel (ell : ∀ j, E j→V j) (e:Sigma E) : ∀ j,V j :=
  Pi.single e.1 (ell e.1 e.2)

/-- The global code does not use component products as precomputed observables.
Raw columns are summed into disjoint fibres and projection commutes exactly
with selecting physical band states. -/
private theorem project_joint_columns (ell : ∀ j,E j→V j) (s:Sigma E→Bool) (j:J) :
    (columns (F:=K) (jointLabel ell) (selected s)).map (LinearMap.proj j) =
      columns (F:=K) (ell j) (selected (fun e=>s ⟨j,e⟩)) := by
  classical
  unfold columns
  rw [Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨⟨c,e⟩,h,rfl⟩,rfl⟩
    by_cases hc : j=c
    · subst c
      change Pi.single j (ell j e) j ∈ _
      rw [Pi.single_eq_same]
      exact Submodule.subset_span ⟨e,(mem_selected_iff (fun e=>s ⟨j,e⟩) e).2 ((mem_selected_iff s ⟨j,e⟩).1 h),rfl⟩
    · change Pi.single c (ell c e) j ∈ _
      rw [Pi.single_eq_of_ne hc]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,h,rfl⟩
    exact Submodule.subset_span ⟨jointLabel ell ⟨j,e⟩,⟨⟨j,e⟩,(mem_selected_iff s ⟨j,e⟩).2 ((mem_selected_iff (fun e=>s ⟨j,e⟩) e).1 h),rfl⟩,by
      change Pi.single j (ell j e) j=ell j e
      exact Pi.single_eq_same _ _⟩

/-- One marginal-moment lattice, for the *global* direct sum (and all its
quotients), simultaneously reconstructs products of arbitrary functions
of the actual selected component-column spans. -/
private theorem joint_moment_reconstruction
    [Fintype (∀ j,V j)]
    [Fintype (Submodule K (∀ j,V j))]
    [∀ L : Submodule K (∀ j,V j),Fintype (Module.Dual K ((∀ j,V j) ⧸ L))]
    (ell : ∀ j,E j→V j) (f : ∀ j,Submodule K (V j) → ℝ) :
    ∃ α : Submodule K (∀ j,V j) → ℝ,
      ∀ s : Sigma E→Bool,
        signedCoeff (jointLabel ell) α (selected s) =
          ∏ j, f j (columns (F:=K) (ell j) (selected (fun e=>s ⟨j,e⟩))) := by
  let F (W : Submodule K (∀ j,V j)) : ℝ := ∏ j, f j (W.map (LinearMap.proj j))
  obtain ⟨α,hα⟩ := physical_lattice_reconstruction (jointLabel ell) F
  refine ⟨α,fun s=>?_⟩
  rw [show signedCoeff (jointLabel ell) α (selected s) =
      F (columns (F:=K) (jointLabel ell) (selected s)) from hα _]
  unfold F
  simp_rw [project_joint_columns]

end Joint

end JointColumns

section AllRibbonMoments

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
variable (G A:X→X) (m:BandFlag E→X)
  (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (t:E→Bool)

abbrev EdgeFibre (j:Components G A m) := fibre (edgeComponent G A m) j

structure ChartFibre (j:Components G A m) where
  state : EdgeFibre G A m j → Bool
  chart : SignedMarkedChart (localGap G A m j)
    (markedAction (localCap G A m j) (localMark G A m h0 j) (fun e=>t e.val) state)
    (markedAction (localCap G A m j) (localMark G A m h0 j) (fun e=>t e.val) (fun e=>!(state e)))
    (EdgeFibre G A m j) (fun e x=>∃ q:Bool×Bool,x=localMark G A m h0 j (e,q))

variable {G A m h0 t}

abbrev chartSpace {j:Components G A m} (C : ChartFibre G A m h0 t j) :=
  SignedLabelSpace C.chart.ports.a C.chart.ports.b C.chart.twist

private theorem exists_fibre_chart (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m)
    (j:Components G A m) : Nonempty (ChartFibre G A m h0 t j) := by
  classical
  obtain ⟨x⟩ := actual_component_nonempty G A m j
  let g := localGap G A m j
  let a := localCap G A m j
  let m' := localMark G A m h0 j
  let t' : EdgeFibre G A m j→Bool := fun e=>t e.val
  have gi := localGap_involution G A m hG j
  have ai := localCap_involution G A m hA j
  have gf (y) : g y≠y := fun h=>hGf y.val (congrArg Subtype.val h)
  have af (y) : a y≠y := fun h=>hAf y.val (congrArg Subtype.val h)
  have mi := localMark_injective G A m hm h0 j
  have hcap := localCap_mark G A m h0 j
  let l := (Finset.univ : Finset (EdgeFibre G A m j)).toList
  obtain ⟨τ,_,hτ⟩ := marked_forest_state g a gi gf ai af m' mi hcap t' (fun _=>false)
      l (Finset.nodup_toList _) (fun _ _=>rfl)
  have hzero : markedAction a m' t' (fun _=>false)=a := by
    funext y
    by_cases h : ∃ q,m' q=y
    · obtain ⟨q,rfl⟩ := h
      rw [markedAction_apply_mark _ _ mi]
      exact (hcap q).symm
    · exact markedAction_apply_unmarked _ _ _ _ _ h
  have hc (y) : wholeConn g (markedAction a m' t' τ) x y := by
    apply (hτ x y).mpr
    rw [hzero]
    exact actual_component_connected G A m h0 j x y
  have hB := markedAction_match a m' ai af mi hcap t' τ
  let P := alternating_flag_chart g (markedAction a m' t' τ) gi hB.1 gf hB.2 x hc
  exact ⟨⟨τ,canonical_marked_signed_chart g a ai af m' mi hcap t' τ P⟩⟩

noncomputable def chartCharge {j:Components G A m} (C : ChartFibre G A m h0 t j)
    (d:ℝ) (W:Submodule K (chartSpace C)) : ℝ :=
  let a := C.chart.ports.a
  let b := C.chart.ports.b
  let B0 := signedBilin a b C.chart.twist
  let hs : B0.flip=B0 := signedBilin_symmetric a b C.chart.twist
    C.chart.ports.a_inj C.chart.ports.b_inj C.chart.ports.separate C.chart.ports.ordered
  (d⁻¹)^Module.finrank K ((radicalForm B0 hs).restrict W).range

private theorem local_charge_counts (hG:Function.Involutive G) (hA:Function.Involutive A)
    (hAf:∀ x,A x≠x) (hm:Function.Injective m) {j:Components G A m}
    (C : ChartFibre G A m h0 t j) (d:ℝ) (hd:d≠0) (s:EdgeFibre G A m j→Bool) :
    (d*d^(selected s).card)*chartCharge C d
      (columns (F:=K) (intrinsicLabel C.chart.ports.a C.chart.ports.b C.chart.twist) (selected s)) =
      d^(markedCircleCount (localGap G A m j) (localCap G A m j)
          (localMark G A m h0 j) (fun e=>t e.val) (switch C.state s)) := by
  classical
  let a := C.chart.ports.a
  let b := C.chart.ports.b
  let B0 := signedBilin a b C.chart.twist
  let hs : B0.flip=B0 := signedBilin_symmetric a b C.chart.twist
    C.chart.ports.a_inj C.chart.ports.b_inj C.chart.ports.separate C.chart.ports.ordered
  let B := radicalForm B0 hs
  let ell := intrinsicLabel a b C.chart.twist
  let W := columns (F:=K) ell (selected s)
  have hc := restriction_euler_from_labels a b C.chart.twist ell B
    C.chart.ports.a_inj C.chart.ports.b_inj C.chart.ports.separate C.chart.ports.ordered
    (fun i j => by
      change B (B0.ker.mkQ (Pi.single j 1)) (B0.ker.mkQ (Pi.single i 1)) = _
      exact (radicalForm_apply B0 hs _ _).trans (signedBilin_port a b C.chart.twist i j)) (selected s)
  have hr := physical_chart_counts (localGap G A m j) (localCap G A m j)
    (localGap_involution G A m hG j) (localCap_involution G A m hA j)
    (fun x h=>hAf x.val (congrArg Subtype.val h))
    (localMark G A m h0 j) (localMark_injective G A m hm h0 j) (localCap_mark G A m h0 j)
    (fun e=>t e.val) C.state s C.chart
  change (d*d^(selected s).card)*(d⁻¹)^Module.finrank K (B.restrict W).range = _
  rw [hr, show d*d^(selected s).card = d^(1+(selected s).card) by rw [pow_add,pow_one],← hc]
  dsimp only [W]
  rw [pow_add,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hd),mul_one]

variable (G A m h0 t)

abbrev AllCharts := ∀ j:Components G A m, ChartFibre G A m h0 t j
abbrev AllEdges := Sigma (EdgeFibre G A m)
abbrev AllSpace (C:AllCharts G A m h0 t) := ∀ j:Components G A m, chartSpace (C j)

noncomputable def allSpaceFinite (C:AllCharts G A m h0 t) : Fintype (AllSpace G A m h0 t C) := by
  classical
  letI : ∀ j:Components G A m, Fintype (chartSpace (C j)) := fun j=>intrinsicFinite (C j).chart.ports.a (C j).chart.ports.b (C j).chart.twist
  infer_instance

noncomputable def allSubspaces (C:AllCharts G A m h0 t) : Fintype (Submodule K (AllSpace G A m h0 t C)) := by
  letI := allSpaceFinite G A m h0 t C
  letI : Finite (Submodule K (AllSpace G A m h0 t C)) :=
    Finite.of_injective (fun W : Submodule K (AllSpace G A m h0 t C) => (W : Set (AllSpace G A m h0 t C)))
      SetLike.coe_injective
  exact Fintype.ofFinite _

noncomputable def allDuals (C:AllCharts G A m h0 t)
    (L : Submodule K (AllSpace G A m h0 t C)) :
    Fintype (Module.Dual K (AllSpace G A m h0 t C ⧸ L)) := by
  letI := allSpaceFinite G A m h0 t C
  letI : Finite (AllSpace G A m h0 t C ⧸ L) := Finite.of_surjective _ L.mkQ_surjective
  letI : Finite (Module.Dual K (AllSpace G A m h0 t C ⧸ L)) :=
    Finite.of_injective (fun f : Module.Dual K (AllSpace G A m h0 t C ⧸ L)=>fun x=>f x)
      (fun {_ _} h=>LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

noncomputable def allLabel (C:AllCharts G A m h0 t) :
    AllEdges G A m → AllSpace G A m h0 t C := by
  classical
  exact jointLabel (fun j=>intrinsicLabel (C j).chart.ports.a (C j).chart.ports.b (C j).chart.twist)

def globalSwitch (C:AllCharts G A m h0 t) (s:AllEdges G A m→Bool) (e:E) : Bool :=
  let e' := fibreEquiv (edgeComponent G A m) e
  switch (C e'.1).state (fun f=>s ⟨e'.1,f⟩) e'.2

noncomputable def jointReadout (C:AllCharts G A m h0 t)
    (α:Submodule K (AllSpace G A m h0 t C)→ℝ) (s:AllEdges G A m→Bool) : ℝ := by
  classical
  letI := allSubspaces G A m h0 t C
  letI := allDuals G A m h0 t C
  exact signedCoeff (allLabel G A m h0 t C) α (selected s)

/-- One global quotient-code physical moment portfolio for arbitrary marked
ribbons, with no connectedness, chart, forest or component premises. -/
private theorem all_ribbon_joint_moments (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m) :
    ∃ C : AllCharts G A m h0 t, ∀ d:ℝ,d≠0 →
      ∃ α:Submodule K (AllSpace G A m h0 t C)→ℝ, ∀ s:AllEdges G A m→Bool,
        (∏ j:Components G A m, d*d^(selected (fun e:EdgeFibre G A m j=>s ⟨j,e⟩)).card)*
          jointReadout G A m h0 t C α s =
        d^(markedCircleCount G A m t (globalSwitch G A m h0 t C s)) := by
  classical
  let C : AllCharts G A m h0 t := fun j=>
    Classical.choice (exists_fibre_chart (h0:=h0) (t:=t) hG hGf hA hAf hm j)
  refine ⟨C,fun d hd=>?_⟩
  letI := allSpaceFinite G A m h0 t C
  letI := allSubspaces G A m h0 t C
  letI := allDuals G A m h0 t C
  obtain ⟨α,ha⟩ := joint_moment_reconstruction
    (fun j=>intrinsicLabel (C j).chart.ports.a (C j).chart.ports.b (C j).chart.twist)
    (fun j=>chartCharge (C j) d)
  refine ⟨α,fun s=>?_⟩
  have eα : jointReadout G A m h0 t C α s = _ := ha s
  rw [eα,← Finset.prod_mul_distrib,actual_circles_components G A m hm h0,← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  have H := local_charge_counts (h0:=h0) (t:=t) hG hA hAf hm (C j) d hd (fun e=>s ⟨j,e⟩)
  have heq : (fun e:EdgeFibre G A m j=>globalSwitch G A m h0 t C s e.val) =
        switch (C j).state (fun e=>s ⟨j,e⟩) := by
    funext e
    obtain ⟨e,he⟩ := e
    change edgeComponent G A m e = j at he
    subst j
    rfl
  rw [heq]
  exact H


def globalSwitchEquiv (C:AllCharts G A m h0 t) : (AllEdges G A m→Bool) ≃ (E→Bool) where
  toFun := globalSwitch G A m h0 t C
  invFun r e := switch (C e.1).state (fun f=>r f.val) e.2
  left_inv s := by
    funext e
    obtain ⟨j,⟨e,he⟩⟩ := e
    change edgeComponent G A m e = j at he
    subst j
    dsimp [globalSwitch,switch,fibreEquiv]
    cases (C (edgeComponent G A m e)).state ⟨e,rfl⟩ <;> simp
  right_inv r := by
    funext e
    dsimp [globalSwitch,switch,fibreEquiv]
    cases (C (edgeComponent G A m e)).state ⟨e,rfl⟩ <;> simp

/-- Exact weighted consequence over the original, unsplit edge carrier.
A general observable of all bits may be included without any factorization
hypothesis; it is not used to select the chart or the moment coefficients. -/
theorem any_observable_joint_moments (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m) :
    letI := Classical.decEq (AllEdges G A m)
    ∃ C : AllCharts G A m h0 t, ∀ d:ℝ,d≠0 →
      ∃ α:Submodule K (AllSpace G A m h0 t C)→ℝ, ∀ w:(E→Bool)→ℝ,
        (∑ r:E→Bool, w r * d^(markedCircleCount G A m t r)) =
        ∑ s:AllEdges G A m→Bool,
          w (globalSwitch G A m h0 t C s) *
           ((∏ j:Components G A m, d*d^(selected (fun e:EdgeFibre G A m j=>s ⟨j,e⟩)).card)*
            jointReadout G A m h0 t C α s) := by
  classical
  letI : DecidableEq (AllEdges G A m) := Classical.decEq _
  obtain ⟨C,hC⟩ := all_ribbon_joint_moments G A m h0 t hG hGf hA hAf hm
  refine ⟨C,fun d hd=>?_⟩
  obtain ⟨α,hα⟩ := hC d hd
  refine ⟨α,fun w=>?_⟩
  simp_rw [hα]
  symm
  exact Equiv.sum_comp (globalSwitchEquiv G A m h0 t C)
    (fun r=>w r * d^(markedCircleCount G A m t r))

end AllRibbonMoments

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments
