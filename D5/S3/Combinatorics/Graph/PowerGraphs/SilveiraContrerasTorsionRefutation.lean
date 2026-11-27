/- GID: D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.claim; result=D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.result; claim=D5/S3/Combinatorics/Graph/PowerGraphs/SilveiraContrerasTorsionRefutation.claim
   digest: A torsion group with cyclic center has a disconnected proper generalized power graph. -/

import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PowerGraphs.SilveiraContrerasTorsionRefutation

section Wreath

variable {D Q : Type*} [Group D] [Group Q] [DecidableEq Q]

/-- Embed the base group in the coordinate indexed by the acting group's identity. -/
private def oneCoordinate : D →* D ≀ᵣ Q where
  toFun a := ⟨Pi.mulSingle (1 : Q) a, 1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp [Pi.mulSingle_mul, Pi.mul_apply]
    · simp

private theorem oneCoordinate_injective :
    Function.Injective (oneCoordinate : D →* D ≀ᵣ Q) := by
  intro a b h
  have heval := congrArg (fun z : D ≀ᵣ Q => z.left 1) h
  simpa [oneCoordinate] using heval

/-- Every nonidentity shift moves every nonidentity element in the chosen coordinate. -/
private theorem shift_moves_oneCoordinate {q : Q} (hq : q ≠ 1) {a : D} (ha : a ≠ 1) :
    (RegularWreathProduct.inl q : D ≀ᵣ Q) * oneCoordinate a *
        (RegularWreathProduct.inl q)⁻¹ ≠ oneCoordinate a := by
  intro he
  have heval := congrArg (fun z : D ≀ᵣ Q => z.left 1) he
  have hqinv : q⁻¹ ≠ 1 := by simpa using hq
  exact ha (by simpa [oneCoordinate, Pi.mulSingle_eq_of_ne hqinv] using heval.symm)

end Wreath

section DirectLimit

variable {G : ℕ → Type*} [∀ i, Group (G i)]
variable (f : ∀ i j : ℕ, i ≤ j → G i →* G j) [DirectedSystem G (f · · ·)]

/-- The map from a given stage to the direct limit. -/
private noncomputable def stageHom (i : ℕ) : G i →* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (DirectLimit.one_def (f := f) i).symm
  map_mul' x y := (DirectLimit.mul_def (f := f) i x y).symm

private theorem stageHom_injective
    (hf : ∀ i j (h : i ≤ j), Function.Injective (f i j h)) (i : ℕ) :
    Function.Injective (stageHom f i) :=
  DirectLimit.mk_injective f hf i

/-- Lift a finite list into one stage, keeping its order and multiplicities. -/
private theorem exists_list_in_stage (xs : List (DirectLimit G f)) :
    ∃ (i : ℕ) (ys : List (G i)), ys.map (stageHom f i) = xs := by
  induction xs with
  | nil => exact ⟨0, [], rfl⟩
  | cons x xs ih =>
    obtain ⟨i, a, ha⟩ := DirectLimit.exists_eq_mk f x
    obtain ⟨j, ys, rfl⟩ := ih
    let k := Nat.max i j
    have hik : i ≤ k := Nat.le_max_left i j
    have hjk : j ≤ k := Nat.le_max_right i j
    refine ⟨k, f i k hik a :: ys.map (f j k hjk), ?_⟩
    rw [List.map_cons, List.map_map, List.cons.injEq]
    refine ⟨(DirectLimit.mk_apply i k a hik).trans ha.symm, ?_⟩
    apply List.map_congr_left
    intro b _
    exact DirectLimit.mk_apply j k b hjk

end DirectLimit

open scoped commutatorElement

/-- In a finite 2-group an odd list of conjugates of a nonidentity element
has nonidentity product. -/
private theorem odd_conjugate_list_prod_ne_one {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) {a : G} (ha : a ≠ 1) (xs : List G)
    (hodd : Odd xs.length) (hconj : ∀ x ∈ xs, IsConj a x) :
    xs.prod ≠ 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hG.isNilpotent
  let L := (⊤ : Subgroup G).lowerCentralSeries
  have hex : ∃ i, a ∉ L i := ⟨n, by simpa [L, hn] using ha⟩
  have hzero : a ∈ L 0 := Subgroup.mem_top a
  have hfind_ne : Nat.find hex ≠ 0 := by
    intro he
    exact (Nat.find_spec hex) (by simpa only [he] using hzero)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
  have hk_mem : a ∈ L k := by
    by_contra h
    have hle := Nat.find_min' hex h
    omega
  have hk_next : a ∉ L (k + 1) := by
    change a ∉ L k.succ
    rw [← hk]
    exact Nat.find_spec hex
  let q := QuotientGroup.mk' (L (k + 1))
  have hq_ne : q a ≠ 1 := fun h => hk_next ((QuotientGroup.eq_one_iff a).mp h)
  have hq_comm (g : G) : Commute (q a) (q g) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅a, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator hk_mem (Subgroup.mem_top g)
  have himage (x : G) (hx : IsConj a x) : q x = q a := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    rw [map_mul, map_mul, map_inv, ← (hq_comm g).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hprod (ys : List G) (hy : ∀ y ∈ ys, IsConj a y) :
      q ys.prod = q a ^ ys.length := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      rw [List.prod_cons, map_mul, himage y (hy y (by simp)),
        ih (fun z hz => hy z (List.mem_cons_of_mem _ hz)), List.length_cons, pow_succ']
  intro heq
  have hpow : q a ^ xs.length = 1 := by rw [← hprod xs hconj, heq, map_one]
  have htwo : 2 ∣ xs.length :=
    ((hG.to_quotient (L (k + 1))).dvd_orderOf hq_ne).trans (orderOf_dvd_of_pow_eq_one hpow)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr htwo)

private abbrev C₂ := Multiplicative (ZMod 2)
private abbrev Stage := IteratedWreathProduct C₂

private def flip : C₂ := Multiplicative.ofAdd 1

private theorem flip_ne_one : flip ≠ 1 := by decide

private theorem card_c₂ : Nat.card C₂ = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]

private theorem stage_isPGroup (n : ℕ) : IsPGroup 2 (Stage n) :=
  IsPGroup.of_card (by rw [IteratedWreathProduct.card, card_c₂])

private def step (n : ℕ) : Stage n →* Stage (n + 1) := oneCoordinate

private def transition (i j : ℕ) (h : i ≤ j) : Stage i →* Stage j :=
  Nat.leRecOn (C := fun k => Stage i →* Stage k) h
    (fun {k} f => (step k).comp f) (MonoidHom.id _)

private theorem transition_succ (i j : ℕ) (h : i ≤ j) :
    transition i (j + 1) (Nat.le_succ_of_le h) = (step j).comp (transition i j h) :=
  Nat.leRecOn_succ h _

private theorem transition_self (i : ℕ) : transition i i le_rfl = MonoidHom.id _ :=
  Nat.leRecOn_self _

private instance towerDirectedSystem : DirectedSystem Stage (transition · · ·) where
  map_self {i} x := by rw [transition_self]; rfl
  map_map {k j i} hij hjk x := by
    induction k, hjk using Nat.le_induction with
    | base => rw [transition_self]; rfl
    | succ k hjk ih =>
      rw [transition_succ j k hjk, transition_succ i k (hij.trans hjk)]
      exact congrArg (step k) ih

private theorem transition_injective (i j : ℕ) (h : i ≤ j) :
    Function.Injective (transition i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [transition_self]; exact Function.injective_id
  | succ j h ih =>
    rw [transition_succ i j h]
    exact oneCoordinate_injective.comp ih

private abbrev H := DirectLimit Stage transition

private noncomputable def incl (i : ℕ) : Stage i →* H := stageHom transition i

private theorem incl_injective (i : ℕ) : Function.Injective (incl i) :=
  stageHom_injective transition transition_injective i

private def shift (i : ℕ) : Stage (i + 1) := RegularWreathProduct.inl flip

private theorem shift_ne_one (i : ℕ) : shift i ≠ 1 := by
  intro h
  exact flip_ne_one (congrArg (fun w : Stage (i + 1) => w.right) h)

private theorem incl_step (i : ℕ) (a : Stage i) : incl (i + 1) (step i a) = incl i a := by
  have h := DirectLimit.mk_apply (f := transition) i (i + 1) a (Nat.le_succ i)
  change incl (i + 1) (transition i (i + 1) (Nat.le_succ i) a) = incl i a at h
  simpa only [transition_succ i i le_rfl, transition_self, MonoidHom.comp_apply, MonoidHom.id_apply] using h

private theorem limit_torsion (x : H) : IsOfFinOrder x := by
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk transition x
  exact (incl_injective i).isOfFinOrder_iff.mpr ((stage_isPGroup i).isOfFinOrder (by decide) a)

private theorem limit_center_eq_one {x : H} (hx : x ∈ Subgroup.center H) : x = 1 := by
  by_contra hxne
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk transition x
  change incl i a ≠ 1 at hxne
  change incl i a ∈ Subgroup.center H at hx
  have ha : a ≠ 1 := fun h => hxne (h ▸ map_one (incl i))
  have hcomm := Subgroup.mem_center_iff.mp hx (incl (i + 1) (shift i))
  rw [← incl_step i a, ← map_mul, ← map_mul] at hcomm
  have heq := incl_injective (i + 1) hcomm
  apply shift_moves_oneCoordinate flip_ne_one ha
  change shift i * step i a * (shift i)⁻¹ = step i a
  rw [heq, mul_assoc, mul_inv_cancel, mul_one]

private theorem exists_limit_ne_one : ∃ x : H, x ≠ 1 :=
  ⟨incl 1 (shift 0), fun h => shift_ne_one 0 (incl_injective 1 (h.trans (map_one _).symm))⟩

private def conjugateProduct {G : Type*} [Group G] (a : G) (gs : List G) : G :=
  (gs.map fun g => g⁻¹ * a * g).prod

private theorem map_conjugateProduct {G K : Type*} [Group G] [Group K]
    (f : G →* K) (a : G) (gs : List G) :
    f (conjugateProduct a gs) = conjugateProduct (f a) (gs.map f) := by
  simp [conjugateProduct, map_list_prod, List.map_map, Function.comp_def]

private theorem limit_odd_conjugateProduct {a : H} (ha : a ≠ 1) (gs : List H)
    (hodd : Odd gs.length) : conjugateProduct a gs ≠ 1 := by
  obtain ⟨i, ys, hys⟩ := exists_list_in_stage transition (a :: gs)
  change ys.map (incl i) = a :: gs at hys
  rcases ys with _ | ⟨b, ks⟩
  · simp at hys
  simp only [List.map_cons, List.cons.injEq] at hys
  obtain ⟨rfl, rfl⟩ := hys
  have hb : b ≠ 1 := fun h => ha (h ▸ map_one (incl i))
  have hs : conjugateProduct b ks ≠ 1 := by
    apply odd_conjugate_list_prod_ne_one (stage_isPGroup i) hb
    · simpa using hodd
    · intro y hy
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hy
      exact isConj_iff.mpr ⟨g⁻¹, by simp⟩
  intro heq
  apply hs
  apply incl_injective i
  rw [map_conjugateProduct, heq, map_one]

/-- The paper’s undirected graph on the nonidentity elements. -/
private def properPowerGraph (G : Type*) [Group G] : SimpleGraph {x : G // x ≠ 1} where
  Adj x y := x ≠ y ∧ ((∃ gs : List G, conjugateProduct x.val gs = y.val) ∨
    (∃ gs : List G, conjugateProduct y.val gs = x.val))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The affirmative statement in Problem 4.3, arXiv:2611.17525v1. -/
def claim : Prop :=
  ∀ (G : Type) [Group G], (∀ x : G, IsOfFinOrder x) →
    IsCyclic (Subgroup.center G) → (properPowerGraph G).Connected ∧
      (properPowerGraph G).ediam ≤ 4

private abbrev Countergroup := H × C₂

private theorem countergroup_torsion (x : Countergroup) : IsOfFinOrder x :=
  IsOfFinOrder.prod_iff.mpr ⟨limit_torsion x.1, isOfFinOrder_of_finite x.2⟩

private theorem countergroup_center_cyclic : IsCyclic (Subgroup.center Countergroup) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic C₂ := isCyclic_of_prime_card card_c₂
  let proj := (MonoidHom.snd H C₂).comp (Subgroup.center Countergroup).subtype
  have first_eq_one (x : Subgroup.center Countergroup) : x.val.1 = 1 := by
    apply limit_center_eq_one
    exact Subgroup.mem_center_iff.mpr fun h =>
      congrArg Prod.fst (Subgroup.mem_center_iff.mp x.property (h, 1))
  apply isCyclic_of_injective proj
  intro x y h
  apply Subtype.ext
  exact Prod.ext ((first_eq_one x).trans (first_eq_one y).symm) h

private theorem flip_order : orderOf flip = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) flip_ne_one

private theorem c₂_pow_eq_one_or_self (a : C₂) (n : ℕ) : a ^ n = 1 ∨ a ^ n = a := by
  have heq := pow_mod_natCard a n
  rw [card_c₂] at heq
  rw [← heq]
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hp | hp <;> simp [hp]

private theorem conjugateProduct_of_central {G : Type*} [Group G] {a : G} (ha : a ∈ Subgroup.center G) (gs : List G) :
    conjugateProduct a gs = a ^ gs.length := by
  induction gs with
  | nil => simp [conjugateProduct]
  | cons g gs ih =>
    change g⁻¹ * a * g * conjugateProduct a gs = a ^ (gs.length + 1)
    rw [show g⁻¹ * a * g = a by rw [Subgroup.mem_center_iff.mp ha g⁻¹, mul_assoc, inv_mul_cancel, mul_one],
      ih, pow_succ']

private noncomputable def central : Countergroup := (1, flip)

private theorem central_ne_one : central ≠ 1 := fun h => flip_ne_one (congrArg Prod.snd h)

private theorem central_mem_center : central ∈ Subgroup.center Countergroup := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  exact Prod.ext (by simp [central]) (mul_comm x.2 flip)

private theorem no_product_from_central {x : Countergroup} (hx : x ≠ 1) (hxc : x ≠ central)
    (gs : List Countergroup) : conjugateProduct central gs ≠ x := by
  rw [conjugateProduct_of_central central_mem_center]
  intro heq
  have hfst : x.1 = 1 := by
    simpa [central] using (congrArg (MonoidHom.fst H C₂) heq).symm
  have hsnd : flip ^ gs.length = x.2 := by
    simpa [central] using congrArg (MonoidHom.snd H C₂) heq
  rcases c₂_pow_eq_one_or_self flip gs.length with hp | hp
  · exact hx (Prod.ext hfst (hsnd.symm.trans hp))
  · exact hxc (Prod.ext hfst (hsnd.symm.trans hp))

private theorem no_product_to_central {x : Countergroup} (hxc : x ≠ central)
    (gs : List Countergroup) : conjugateProduct x gs ≠ central := by
  intro heq
  have hsnd := congrArg (MonoidHom.snd H C₂) heq
  rw [map_conjugateProduct, conjugateProduct_of_central (Subgroup.mem_center_iff.mpr
    (mul_comm · _)), List.length_map] at hsnd
  change x.2 ^ gs.length = flip at hsnd
  have hx₂ : x.2 = flip := by
    rcases c₂_pow_eq_one_or_self x.2 gs.length with hp | hp
    · exact (flip_ne_one (hsnd.symm.trans hp)).elim
    · exact hp.symm.trans hsnd
  have hodd : Odd gs.length := by
    apply Nat.not_even_iff_odd.mp
    intro heven
    have hdvd : orderOf flip ∣ gs.length := by
      rw [flip_order]
      exact even_iff_two_dvd.mp heven
    have hp : flip ^ gs.length = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [hx₂, hp] at hsnd
    exact flip_ne_one hsnd.symm
  have hx₁ : x.1 ≠ 1 := fun h => hxc (Prod.ext h hx₂)
  have hfst := congrArg (MonoidHom.fst H C₂) heq
  rw [map_conjugateProduct] at hfst
  exact limit_odd_conjugateProduct hx₁ _ (by rwa [List.length_map]) hfst

private noncomputable def centralVertex : {x : Countergroup // x ≠ 1} := ⟨central, central_ne_one⟩

private theorem central_isolated (x : {x : Countergroup // x ≠ 1}) :
    ¬ (properPowerGraph Countergroup).Adj centralVertex x := by
  rintro ⟨hne, ⟨gs, hgs⟩ | ⟨gs, hgs⟩⟩
  · exact no_product_from_central x.property (fun h => hne (Subtype.ext h.symm)) gs hgs
  · exact no_product_to_central (fun h => hne (Subtype.ext h.symm)) gs hgs

private theorem countergroup_disconnected : ¬ (properPowerGraph Countergroup).Connected := by
  intro hconn
  obtain ⟨a, ha⟩ := exists_limit_ne_one
  let other : {x : Countergroup // x ≠ 1} :=
    ⟨(a, 1), fun h => ha (congrArg Prod.fst h)⟩
  have hne : centralVertex ≠ other := fun h =>
    flip_ne_one (congrArg (fun x => x.val.2) h)
  obtain ⟨walk⟩ := hconn centralVertex other
  obtain ⟨_, h, _, _⟩ := walk.exists_eq_cons_of_ne hne
  exact central_isolated _ h

/-- The central involution has no neighbors, and the graph has a second vertex. -/
theorem result : ¬ claim := by
  intro h
  exact countergroup_disconnected (h Countergroup countergroup_torsion countergroup_center_cyclic).1

end D5.S3.Combinatorics.Graph.PowerGraphs.SilveiraContrerasTorsionRefutation
