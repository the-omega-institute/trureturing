/- GID: D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings
   generality: I
   mirror-B: D5/B/S0/Certificates/Groups/AraujoSymmetricCompleteMappings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.result; premises=D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.signs_two,D5/S0/Certificates/Groups/AraujoSymmetricCompleteMappings.signs_three
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings.symmetric_small_or_large
proof_shape: content — symmetric_option_lift, symmetric_complete_step, symmetric_complete_mapping, symmetric_small_or_large
proof_shape: bind-only — complete_mapping_of_idempotent, complete_mapping_transport, complete_mapping_character_product, signs_two, signs_three, symmetric_two_no_complete, symmetric_three_no_complete, bijective_predicate_forward, complete_mapping_preserves_units, complete_mapping_restrict_units, complete_mapping_of_parametrization, fourEnum, fourAlpha, symmetric_four_complete, DiagonalTransversal, diagonalTransversalGood, diagonalTransversalTransport, diagonalTransversalProduct, diagonalTransversalTables, packetGroup2, packetEnum2, packetAlpha2, packetTheta2, diagonalTransversalS2, packetGroup3, packetEnum3, packetAlpha3, packetTheta3, diagonalTransversalS3, diagonalTransversalFiniteGood, diagonalTransversalFiniteEven, reesProduct, ReesTransversal, diagonalTransversal_rees, DiagonalTransversal.alpha, DiagonalTransversal.theta, DiagonalTransversal.alphaFirst, DiagonalTransversal.thetaFirst, DiagonalTransversal.thetaLast, DiagonalTransversal.thetaGroup, ReesTransversal.alpha, ReesTransversal.theta, ReesTransversal.product
Direct frozen dependencies (declaration statement_id):
D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation.CompleteMapping sha256:feb39c68be69503661ae3a788bf2232ca9855f0eaebeaa2ddd409e15b0143e47
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24053
-/

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.DedekindFinite
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.LibrarySearch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Order.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Lucas
import D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings

open Equiv
open scoped BigOperators
open D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation


theorem complete_mapping_of_idempotent {S : Type} [Semigroup S]
    (hS : ∀ x : S, x * x = x) : CompleteMapping (id : S → S) := by
  refine ⟨Function.bijective_id, ?_⟩
  change Function.Bijective (fun x : S => x * x)
  rw [show (fun x : S => x * x) = id from funext hS]
  exact Function.bijective_id

theorem complete_mapping_transport {S T : Type} [Semigroup S] [Semigroup T]
    (e : S ≃* T) {a : S → S} (ha : CompleteMapping a) :
    CompleteMapping (fun y : T => e (a (e.symm y))) := by
  refine ⟨e.bijective.comp (ha.1.comp e.symm.bijective), ?_⟩
  have hprod : (fun y : T => y * e (a (e.symm y))) =
      fun y : T => e (e.symm y * a (e.symm y)) := by
    funext y
    rw [map_mul, e.apply_symm_apply]
  rw [hprod]
  exact e.bijective.comp (ha.2.comp e.symm.bijective)


private theorem complete_mapping_character_product {G A : Type} [Group G] [Fintype G]
    [CommGroup A] (χ : G →* A) {a : G → G} (ha : CompleteMapping a) :
    (∏ g : G, χ g) = 1 := by
  have halpha := ha.1.prod_comp χ
  have htheta := ha.2.prod_comp χ
  have htotal : (∏ g : G, χ g) = (∏ g : G, χ g) * (∏ g : G, χ g) := by
    calc
      (∏ g : G, χ g) = ∏ g : G, χ (g * a g) := htheta.symm
      _ = (∏ g : G, χ g) * (∏ g : G, χ (a g)) := by
        simp only [map_mul, Finset.prod_mul_distrib]
      _ = (∏ g : G, χ g) * (∏ g : G, χ g) := by rw [halpha]
  exact (mul_left_cancel (a := ∏ g : G, χ g) (by simpa using htotal.symm)).symm

private theorem signs_two : (∏ g : Equiv.Perm (Fin 2), Equiv.Perm.sign g) = -1 := by
  decide

private theorem signs_three : (∏ g : Equiv.Perm (Fin 3), Equiv.Perm.sign g) = -1 := by
  decide

theorem symmetric_two_no_complete :
    ¬ ∃ a : Equiv.Perm (Fin 2) → Equiv.Perm (Fin 2), CompleteMapping a := by
  rintro ⟨a,ha⟩
  have h := complete_mapping_character_product Equiv.Perm.sign ha
  rw [signs_two] at h
  exact (by decide : (-1 : ℤˣ) ≠ 1) h

theorem symmetric_three_no_complete :
    ¬ ∃ a : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3), CompleteMapping a := by
  rintro ⟨a,ha⟩
  have h := complete_mapping_character_product Equiv.Perm.sign ha
  rw [signs_three] at h
  exact (by decide : (-1 : ℤˣ) ≠ 1) h

private theorem bijective_predicate_forward {X : Type*} [Finite X]
    (P : X → Prop) (f : X → X) (hf : Function.Bijective f)
    (hback : ∀ x, P (f x) → P x) : ∀ x, P x → P (f x) := by
  classical
  let e := Equiv.ofBijective f hf
  let b : {x : X // P x} → {x : X // P x} := fun y =>
    ⟨e.symm y, hback _ (by change P (e (e.symm y)); rw [e.apply_symm_apply]; exact y.property)⟩
  have hb : Function.Injective b := by
    intro x y h
    apply Subtype.ext
    exact e.symm.injective (congrArg Subtype.val h)
  intro x hx
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hb ⟨x,hx⟩
  have hi : e.symm y = x := congrArg Subtype.val hy
  have hfx : f x = y := by
    rw [← hi]
    exact e.apply_symm_apply y
  exact hfx ▸ y.property

private theorem complete_mapping_preserves_units {M : Type} [Monoid M] [Finite M]
    {a : M → M} (ha : CompleteMapping a) :
    (∀ x, IsUnit x → IsUnit (x * a x)) ∧
    (∀ x, IsUnit x → IsUnit (a x)) := by
  have ht : ∀ x, IsUnit x → IsUnit (x * a x) :=
    bijective_predicate_forward IsUnit (fun x => x * a x) ha.2
      (fun _ h => isUnit_of_mul_isUnit_left h)
  exact ⟨ht, fun x hx => isUnit_of_mul_isUnit_right (ht x hx)⟩

theorem complete_mapping_restrict_units {M : Type} [Monoid M] [Finite M]
    {a : M → M} (ha : CompleteMapping a) :
    ∃ aU : Mˣ → Mˣ, CompleteMapping aU := by
  classical
  letI : Finite Mˣ := Finite.of_injective Units.val Units.val_injective
  let aU : Mˣ → Mˣ := fun u => (complete_mapping_preserves_units ha).2 u u.isUnit |>.unit
  have hval : ∀ u, (aU u : M) = a (u : M) := fun _ => rfl
  have hai : Function.Injective aU := by
    intro x y h
    apply Units.ext
    exact ha.1.1 (by simpa only [hval] using congrArg Units.val h)
  have hti : Function.Injective (fun u : Mˣ => u * aU u) := by
    intro x y h
    apply Units.ext
    exact ha.2.1 (by simpa only [Units.val_mul, hval] using congrArg Units.val h)
  exact ⟨aU, ⟨hai, Finite.surjective_of_injective hai⟩,
    ⟨hti, Finite.surjective_of_injective hti⟩⟩


/-- A transversal parametrization is sufficient to construct a complete mapping. -/
private theorem complete_mapping_of_parametrization {G X : Type} [Semigroup G]
    (e : X ≃ G) (b : X → G) (hb : Function.Bijective b)
    (hp : Function.Bijective (fun x => e x * b x)) :
    ∃ a : G → G, CompleteMapping a := by
  refine ⟨fun g => b (e.symm g), hb.comp e.symm.bijective, ?_⟩
  have he : (fun g => g * b (e.symm g)) =
      (fun x => e x * b x) ∘ e.symm := by
    funext g
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [he]
  exact hp.comp e.symm.bijective

/-- Elementary symmetric-group induction using swap representatives and a derangement. -/
private theorem symmetric_option_lift {X : Type} [Fintype X] [DecidableEq X]
    (s : Perm X) (hs : ∀ x, s x ≠ x)
    (ha : ∃ a : Perm X → Perm X, CompleteMapping a) :
    ∃ b : Perm (Option X) → Perm (Option X), CompleteMapping b := by
  obtain ⟨a, ha⟩ := ha
  let e : Option X × Perm X ≃ Perm (Option X) := Perm.decomposeOption.symm
  let b : Option X × Perm X → Perm (Option X) := fun x =>
    e ((x.2.optionCongr).symm (s.optionCongr x.1), a x.2)
  have hb : Function.Injective b := by
    rintro ⟨i,p⟩ ⟨j,q⟩ h
    have h' := e.injective h
    have hp : p = q := ha.1.1 (congrArg Prod.snd h')
    subst q
    have hij : i = j := s.optionCongr.injective
      (p.optionCongr.symm.injective (congrArg Prod.fst h'))
    exact Prod.ext hij rfl
  have hprod (i : Option X) (p : Perm X) :
      e (i,p) * b (i,p) =
        swap none i * swap none (s.optionCongr i) * (p * a p).optionCongr := by
    dsimp [e,b,Perm.decomposeOption]
    have hm : p.optionCongr * swap none (p.optionCongr.symm (s.optionCongr i)) =
        swap none (s.optionCongr i) * p.optionCongr := by
      simpa using Equiv.mul_swap_eq_swap_mul p.optionCongr none
        (p.optionCongr.symm (s.optionCongr i))
    rw [mul_assoc, ← mul_assoc p.optionCongr, hm]
    simp only [mul_assoc]
    congr 2
    ext x
    cases x <;> rfl
  have ht (i : Option X) : swap none i (s.optionCongr i) = s.optionCongr i := by
    cases i with
    | none => simp
    | some i =>
      exact swap_apply_of_ne_of_ne (by simp) (by simpa using hs i)
  have hpi : Function.Injective (fun x : Option X × Perm X => e x * b x) := by
    rintro ⟨i,p⟩ ⟨j,q⟩ h
    simp only [hprod] at h
    have hi : i = j := by
      apply s.optionCongr.injective
      have hn := congrArg (fun f : Perm (Option X) => f none) h
      have hz (u : Perm X) : u.optionCongr (none : Option X) = none := rfl
      simpa only [Perm.mul_apply,hz,swap_apply_left,ht] using hn
    subst j
    have hpq : (p * a p).optionCongr = (q * a q).optionCongr :=
      mul_left_cancel h
    exact Prod.ext rfl (ha.2.1 (optionCongr_injective hpq))
  apply complete_mapping_of_parametrization e b
  · refine ⟨hb, ?_⟩
    intro y
    obtain ⟨x,hx⟩ := Finite.surjective_of_injective (hb.comp e.symm.injective) y
    exact ⟨e.symm x,hx⟩
  · refine ⟨hpi, ?_⟩
    intro y
    obtain ⟨x,hx⟩ := Finite.surjective_of_injective (hpi.comp e.symm.injective) y
    exact ⟨e.symm x,hx⟩

private noncomputable def fourEnum : Fin 24 → Equiv.Perm (Fin 4) := ![
  Equiv.ofBijective ![0, 1, 2, 3] (by decide),
  Equiv.ofBijective ![0, 1, 3, 2] (by decide),
  Equiv.ofBijective ![0, 2, 1, 3] (by decide),
  Equiv.ofBijective ![0, 2, 3, 1] (by decide),
  Equiv.ofBijective ![0, 3, 1, 2] (by decide),
  Equiv.ofBijective ![0, 3, 2, 1] (by decide),
  Equiv.ofBijective ![1, 0, 2, 3] (by decide),
  Equiv.ofBijective ![1, 0, 3, 2] (by decide),
  Equiv.ofBijective ![1, 2, 0, 3] (by decide),
  Equiv.ofBijective ![1, 2, 3, 0] (by decide),
  Equiv.ofBijective ![1, 3, 0, 2] (by decide),
  Equiv.ofBijective ![1, 3, 2, 0] (by decide),
  Equiv.ofBijective ![2, 0, 1, 3] (by decide),
  Equiv.ofBijective ![2, 0, 3, 1] (by decide),
  Equiv.ofBijective ![2, 1, 0, 3] (by decide),
  Equiv.ofBijective ![2, 1, 3, 0] (by decide),
  Equiv.ofBijective ![2, 3, 0, 1] (by decide),
  Equiv.ofBijective ![2, 3, 1, 0] (by decide),
  Equiv.ofBijective ![3, 0, 1, 2] (by decide),
  Equiv.ofBijective ![3, 0, 2, 1] (by decide),
  Equiv.ofBijective ![3, 1, 0, 2] (by decide),
  Equiv.ofBijective ![3, 1, 2, 0] (by decide),
  Equiv.ofBijective ![3, 2, 0, 1] (by decide),
  Equiv.ofBijective ![3, 2, 1, 0] (by decide)
]
private def fourAlpha : Fin 24 → Fin 24 := ![0, 2, 19, 1, 13, 14, 3, 4, 21, 11, 18, 23, 5, 17, 22, 12, 20, 8, 7, 15, 6, 10, 16, 9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem symmetric_four_complete :
    ∃ a : Perm (Fin 4) → Perm (Fin 4), CompleteMapping a := by
  exact complete_mapping_of_parametrization
    (Equiv.ofBijective fourEnum (by decide)) (fourEnum ∘ fourAlpha)
    (by decide) (by decide)

private theorem symmetric_complete_step {n : ℕ} (hn : 2 ≤ n)
    (ha : ∃ a : Perm (Fin n) → Perm (Fin n), CompleteMapping a) :
    ∃ a : Perm (Fin (n+1)) → Perm (Fin (n+1)), CompleteMapping a := by
  letI : NeZero n := ⟨by omega⟩
  have hd : ∀ x : Fin n, finRotate n x ≠ x := by
    intro x he
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have hh := congrArg Fin.val he
    rw [coe_finRotate] at hh
    split_ifs at hh with hlast
    · have hx : x.val = m := congrArg Fin.val hlast
      omega
    · omega
  obtain ⟨a,ha⟩ := symmetric_option_lift (finRotate n) hd ha
  let e := (finSuccEquiv n).symm.permCongrHom
  exact ⟨_, complete_mapping_transport e ha⟩

private theorem symmetric_complete_mapping (r : ℕ) (hr : 4 ≤ r) :
    ∃ a : Perm (Fin r) → Perm (Fin r), CompleteMapping a := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction k with
  | zero => exact symmetric_four_complete
  | succ k ih => exact symmetric_complete_step (n := 4+k) (by omega) ih

theorem symmetric_small_or_large (r : ℕ) (hr : r ≠ 2 ∧ r ≠ 3) :
    ∃ a : Equiv.Perm (Fin r) → Equiv.Perm (Fin r), CompleteMapping a := by
  by_cases h : 4 ≤ r
  · exact symmetric_complete_mapping r h
  · have h01 : r = 0 ∨ r = 1 := by omega
    rcases h01 with rfl | rfl
    all_goals exact ⟨id,complete_mapping_of_idempotent (fun x => Subsingleton.elim _ _)⟩

structure DiagonalTransversal (I G : Type) [Group G] where
  alpha : Equiv.Perm ((I × G × I))
  theta : Equiv.Perm ((I × G × I))
  alphaFirst : ∀ x, (alpha x).1 = x.2.2
  thetaFirst : ∀ x, (theta x).1 = x.1
  thetaLast : ∀ x, (theta x).2.2 = (alpha x).2.2
  thetaGroup : ∀ x, (theta x).2.1 = x.2.1 * (alpha x).2.1

private noncomputable def diagonalTransversalGood {I G : Type} [Group I] [Group G]
    (a : G → G) (ha : CompleteMapping a) : DiagonalTransversal I G := by
  let ae := Equiv.ofBijective a ha.1
  let te := Equiv.ofBijective (fun g => g * a g) ha.2
  let alpha : Equiv.Perm ((I × G × I)) := {
    toFun := fun x => (x.2.2,ae x.2.1,x.1*x.2.2)
    invFun := fun x => (x.2.2*x.1⁻¹,ae.symm x.2.1,x.1)
    left_inv := by rintro ⟨i,g,d⟩; simp
    right_inv := by rintro ⟨i,g,d⟩; simp }
  let theta : Equiv.Perm ((I × G × I)) := {
    toFun := fun x => (x.1,te x.2.1,x.1*x.2.2)
    invFun := fun x => (x.1,te.symm x.2.1,x.1⁻¹*x.2.2)
    left_inv := by rintro ⟨i,g,d⟩; simp [mul_assoc]
    right_inv := by rintro ⟨i,g,d⟩; simp [mul_assoc] }
  exact ⟨alpha,theta,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩


private noncomputable def diagonalTransversalTransport {I J G : Type} [Group G]
    (e : I ≃ J) (w : DiagonalTransversal I G) : DiagonalTransversal J G := by
  let t : (I × G × I) ≃ (J × G × J) := e.prodCongr ((Equiv.refl G).prodCongr e)
  let alpha := (t.symm.trans w.alpha).trans t
  let theta := (t.symm.trans w.theta).trans t
  refine ⟨alpha,theta,?_,?_,?_,?_⟩
  · intro x
    change e (w.alpha (t.symm x)).1 = x.2.2
    rw [w.alphaFirst]
    exact e.apply_symm_apply _
  · intro x
    change e (w.theta (t.symm x)).1 = x.1
    rw [w.thetaFirst]
    exact e.apply_symm_apply _
  · intro x
    change e (w.theta (t.symm x)).2.2 = e (w.alpha (t.symm x)).2.2
    rw [w.thetaLast]
  · intro x
    change (w.theta (t.symm x)).2.1 = x.2.1 * (w.alpha (t.symm x)).2.1
    exact w.thetaGroup (t.symm x)

private noncomputable def diagonalTransversalProduct {I J G : Type} [Group J] [Group G]
    (w : DiagonalTransversal I G) : DiagonalTransversal (I × J) G := by
  let t : ((I × J) × G × (I × J)) ≃ (I × G × I) × (J × J) :=
    (Equiv.prodProdProdComm I J G (I × J)).trans
      ((Equiv.prodCongr (Equiv.refl (I × G))
        (((Equiv.prodAssoc J I J).symm.trans
          (Equiv.prodCongr (Equiv.prodComm J I) (Equiv.refl J))).trans
            (Equiv.prodAssoc I J J))).trans
        ((Equiv.prodAssoc (I × G) I (J × J)).symm.trans
          (Equiv.prodCongr (Equiv.prodAssoc I G I) (Equiv.refl (J × J)))))
  let alpha := (t.trans (w.alpha.prodCongr ((Equiv.prodComm J J).trans
    (Equiv.prodCongrRight (fun k => Equiv.mulRight k))))).trans t.symm
  let theta := (t.trans (w.theta.prodCongr (Equiv.prodCongrRight (fun j => Equiv.mulLeft j)))).trans t.symm
  refine ⟨alpha,theta,?_,?_,?_,?_⟩
  · rintro ⟨⟨i,j⟩,g,⟨d,k⟩⟩
    change ((w.alpha (i,g,d)).1,k) = (d,k)
    rw [w.alphaFirst]
  · rintro ⟨⟨i,j⟩,g,⟨d,k⟩⟩
    change ((w.theta (i,g,d)).1,j) = (i,j)
    rw [w.thetaFirst]
  · rintro ⟨⟨i,j⟩,g,⟨d,k⟩⟩
    change ((w.theta (i,g,d)).2.2,j*k) = ((w.alpha (i,g,d)).2.2,j*k)
    rw [w.thetaLast]
  · rintro ⟨⟨i,j⟩,g,⟨d,k⟩⟩
    exact w.thetaGroup (i,g,d)

private noncomputable def diagonalTransversalTables {X I G : Type} [Group G]
    (e : X ≃ (I × G × I)) (a t : Equiv.Perm X)
    (ha : ∀ x, (e (a x)).1 = (e x).2.2)
    (hti : ∀ x, (e (t x)).1 = (e x).1)
    (htl : ∀ x, (e (t x)).2.2 = (e (a x)).2.2)
    (htg : ∀ x, (e (t x)).2.1 = (e x).2.1 * (e (a x)).2.1) :
    DiagonalTransversal I G := by
  let alpha := (e.symm.trans a).trans e
  let theta := (e.symm.trans t).trans e
  refine ⟨alpha,theta,?_,?_,?_,?_⟩
  · intro x; obtain ⟨y,rfl⟩ := e.surjective x
    simpa [alpha] using ha y
  · intro x; obtain ⟨y,rfl⟩ := e.surjective x
    simpa [theta] using hti y
  · intro x; obtain ⟨y,rfl⟩ := e.surjective x
    simpa [alpha,theta] using htl y
  · intro x; obtain ⟨y,rfl⟩ := e.surjective x
    simpa [alpha,theta] using htg y

private noncomputable def packetGroup2 : Fin 2 → Equiv.Perm (Fin 2) := ![
  Equiv.ofBijective ![0, 1] (by decide),
  Equiv.ofBijective ![1, 0] (by decide)
]
private noncomputable def packetEnum2 : Fin 8 → ((Fin 2) × (Equiv.Perm (Fin 2)) × (Fin 2)) := ![
  (0,packetGroup2 0,0),
  (0,packetGroup2 0,1),
  (0,packetGroup2 1,0),
  (0,packetGroup2 1,1),
  (1,packetGroup2 0,0),
  (1,packetGroup2 0,1),
  (1,packetGroup2 1,0),
  (1,packetGroup2 1,1)
]
private def packetAlpha2 : Fin 8 → Fin 8 := ![0, 5, 1, 4, 2, 7, 3, 6]
private def packetTheta2 : Fin 8 → Fin 8 := ![0, 1, 3, 2, 6, 7, 5, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
noncomputable def diagonalTransversalS2 : DiagonalTransversal (Fin 2) (Equiv.Perm (Fin 2)) :=
  diagonalTransversalTables (Equiv.ofBijective packetEnum2 (by decide))
    (Equiv.ofBijective packetAlpha2 (by decide))
    (Equiv.ofBijective packetTheta2 (by decide))
    (by decide) (by decide) (by decide) (by decide)

private noncomputable def packetGroup3 : Fin 6 → Equiv.Perm (Fin 3) := ![
  Equiv.ofBijective ![0, 1, 2] (by decide),
  Equiv.ofBijective ![0, 2, 1] (by decide),
  Equiv.ofBijective ![1, 0, 2] (by decide),
  Equiv.ofBijective ![1, 2, 0] (by decide),
  Equiv.ofBijective ![2, 0, 1] (by decide),
  Equiv.ofBijective ![2, 1, 0] (by decide)
]
private noncomputable def packetEnum3 : Fin 24 → ((Fin 2) × (Equiv.Perm (Fin 3)) × (Fin 2)) := ![
  (0,packetGroup3 0,0),
  (0,packetGroup3 0,1),
  (0,packetGroup3 1,0),
  (0,packetGroup3 1,1),
  (0,packetGroup3 2,0),
  (0,packetGroup3 2,1),
  (0,packetGroup3 3,0),
  (0,packetGroup3 3,1),
  (0,packetGroup3 4,0),
  (0,packetGroup3 4,1),
  (0,packetGroup3 5,0),
  (0,packetGroup3 5,1),
  (1,packetGroup3 0,0),
  (1,packetGroup3 0,1),
  (1,packetGroup3 1,0),
  (1,packetGroup3 1,1),
  (1,packetGroup3 2,0),
  (1,packetGroup3 2,1),
  (1,packetGroup3 3,0),
  (1,packetGroup3 3,1),
  (1,packetGroup3 4,0),
  (1,packetGroup3 4,1),
  (1,packetGroup3 5,0),
  (1,packetGroup3 5,1)
]
private def packetAlpha3 : Fin 24 → Fin 24 := ![0, 13, 1, 17, 2, 12, 4, 15, 3, 16, 5, 14, 6, 20, 7, 21, 8, 18, 11, 19, 9, 22, 10, 23]
private def packetTheta3 : Fin 24 → Fin 24 := ![0, 1, 3, 9, 6, 4, 10, 5, 11, 2, 7, 8, 18, 20, 23, 17, 22, 14, 15, 21, 19, 16, 12, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
noncomputable def diagonalTransversalS3 : DiagonalTransversal (Fin 2) (Equiv.Perm (Fin 3)) :=
  diagonalTransversalTables (Equiv.ofBijective packetEnum3 (by decide))
    (Equiv.ofBijective packetAlpha3 (by decide))
    (Equiv.ofBijective packetTheta3 (by decide))
    (by decide) (by decide) (by decide) (by decide)

noncomputable def diagonalTransversalFiniteGood {I G : Type} [Fintype I] [Nonempty I]
    [Group G] (a : G → G) (ha : CompleteMapping a) : DiagonalTransversal I G := by
  letI : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  let e : I ≃ Multiplicative (ZMod (Fintype.card I)) :=
    (Fintype.equivFin I).trans ((ZMod.finEquiv (Fintype.card I)).toEquiv.trans Multiplicative.ofAdd)
  exact diagonalTransversalTransport e.symm (diagonalTransversalGood a ha)

noncomputable def diagonalTransversalFiniteEven {I G : Type} [Fintype I] [Nonempty I]
    [Group G] (he : Even (Fintype.card I)) (base : DiagonalTransversal (Fin 2) G) :
    DiagonalTransversal I G := by
  let m : ℕ := Classical.choose he
  have hm : Fintype.card I = m + m := Classical.choose_spec he
  have hpos : 0 < m := by have := Fintype.card_pos (α := I); omega
  letI : NeZero m := ⟨by omega⟩
  let e : (Fin 2 × Multiplicative (ZMod m)) ≃ I := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_multiplicative,ZMod.card]
    omega)
  exact diagonalTransversalTransport e (diagonalTransversalProduct base)

noncomputable def reesProduct {I G : Type} [Group G]
    (P : I → I → Option G) (x y : (I × G × I)) : Option ((I × G × I)) :=
  (P x.2.2 y.1).map (fun p => (x.1,x.2.1*p*y.2.1,y.2.2))

structure ReesTransversal {I G : Type} [Group G] (P : I → I → Option G) where
  alpha : Equiv.Perm ((I × G × I))
  theta : Equiv.Perm ((I × G × I))
  product : ∀ x, reesProduct P x (alpha x) = some (theta x)

theorem diagonalTransversal_rees {I G : Type} [Group G]
    (P : I → I → Option G) (hd : ∀ i, P i i = some 1)
    (w : DiagonalTransversal I G) : Nonempty (ReesTransversal P) := by
  refine ⟨⟨w.alpha,w.theta,?_⟩⟩
  intro x
  unfold reesProduct
  rw [w.alphaFirst,hd]
  simp only [Option.map_some,mul_one]
  have ht : w.theta x = (x.1,x.2.1*(w.alpha x).2.1,(w.alpha x).2.2) := by
    apply Prod.ext
    · exact w.thetaFirst x
    · apply Prod.ext
      · exact w.thetaGroup x
      · exact w.thetaLast x
  exact congrArg some ht.symm

end D5.S0.Certificates.Groups.AraujoSymmetricCompleteMappings
