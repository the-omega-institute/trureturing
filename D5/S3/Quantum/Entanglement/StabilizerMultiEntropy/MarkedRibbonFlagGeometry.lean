/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonFlagGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonFlagGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct exact parity switches and numbered literal alternating flag cycles. -/

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

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry

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

theorem mem_selected_iff (s : E → Bool) (e : E) : e ∈ selected s ↔ s e=true := by
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

theorem eqvGen_transfer {R S : X→X→Prop} (hf : ∀ x y, R x y → S x y)
    (hs : Equivalence S) (x y : X) (h : EqvGen R x y) : S x y := by
  induction h with
  | rel x y h => exact hf x y h
  | refl x => exact hs.refl x
  | symm x y _ ih => exact hs.symm ih
  | trans x y z _ _ ih1 ih2 => exact hs.trans ih1 ih2

theorem eqvGen_is_equivalence (R : X→X→Prop) : Equivalence (EqvGen R) :=
  ⟨.refl, fun h=>.symm _ _ h, fun h g=>.trans _ _ _ h g⟩

/-- Switching the two matching edges of two different boundary circles
is exactly adjoining the connection between those circles. Both signs
satisfy the same assumptions, even when an A-edge is also a G-edge. -/
theorem match_switch_join (G A A' : X→X)
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

theorem graphJoin_cons (R : X→X→Prop) (a b : X) (l : List (X×X)) (x y : X) :
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

theorem graphJoin_congr {R S : X→X→Prop} (h : ∀ x y, R x y ↔ S x y)
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
theorem signed_alternative_from_chart (G A : X→X) (C : AlternatingFlagChart G A)
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

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry
