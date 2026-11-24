/- GID: D5/S3/Combinatorics/Matroids/SteinerSwitchQuotient
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerSwitchQuotient
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Central return translations determine the lifted matching components. -/

/-
point_deleted_component_lifts
  proof_shape: content
  admission_basis: escape-witness
  escape_witness: freeness and equivariant returns show that the quotient
    period scales by the order of the return element. Path lifting and equal
    fibre counts give the number of components above a quotient component.
  Direct frozen dependencies: SteinerSwitchCentre.steinerMul and product_comm,
    SteinerAlternatingSwitches.pivotGraph, translate_involutive, and
    AlternatingComponentParity.connected_ncard_eq_two_mul.
-/

import D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
import D5.S3.Combinatorics.PerfectMatchings.AlternatingComponentParity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Alternating components over the central quotient of a Steiner loop
-/

namespace D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient

open D5.S3.Combinatorics.PerfectMatchings
open Function Set SimpleGraph

private theorem card_of_equal_fibres {U V : Type*} [Finite U] [Finite V]
    (f : U → V) (n : ℕ) (hf : ∀ b : V, Nat.card {a // f a = b} = n) :
    Nat.card U = Nat.card V * n := by
  classical
  let _ : Fintype U := Fintype.ofFinite _
  let _ : Fintype V := Fintype.ofFinite _
  let _ : (b : V) → Fintype {a // f a = b} := fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  have count (b : V) : Fintype.card {a // f a = b} = n := by
    rw [← Nat.card_eq_fintype_card, hf]
  simp [count]

private theorem component_count_factor {X Y A : Type*} [Finite X] [Finite Y] [Finite A]
    [Group A] [MulAction A X] (G : SimpleGraph X) (H : SimpleGraph Y) (proj : X → Y)
    (p q : X → X) (P Q : Y → Y)
    (shapeUp : ∀ u v, G.Adj u v ↔ p u = v ∨ q u = v)
    (shapeDown : ∀ u v, H.Adj u v ↔ P u = v ∨ Q u = v)
    (semiP : Semiconj proj p P) (semiQ : Semiconj proj q Q)
    (presP : ∀ (a : A) (y : X), p (a • y) = a • p y)
    (presQ : ∀ (a : A) (y : X), q (a • y) = a • q y)
    (fibre : ∀ u v, proj u = proj v ↔ ∃ a : A, a • u = v)
    (free : ∀ (a : A) (u : X), a • u = u → a = 1)
    (x : X) (s : ℕ)
    (size : (G.connectedComponentMk x).supp.ncard =
      (H.connectedComponentMk (proj x)).supp.ncard * s) :
    let B := (H.connectedComponentMk (proj x)).supp
    let T := Set.range (fun a : proj ⁻¹' B => G.connectedComponentMk a.val)
    T.ncard * s = Nat.card A := by
  classical
  let B := (H.connectedComponentMk (proj x)).supp
  let U := proj ⁻¹' B
  let T := Set.range (fun a : U => G.connectedComponentMk a.val)
  have mapReach {u v : X} (h : G.Reachable u v) : H.Reachable (proj u) (proj v) := by
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Reachable.rfl
    | tail _ edge ih =>
      apply ih.trans
      apply Adj.reachable
      apply (shapeDown _ _).mpr
      rcases (shapeUp _ _).mp edge with rfl | rfl
      · exact Or.inl (semiP _).symm
      · exact Or.inr (semiQ _).symm
  have liftReach (y : Y) (h : H.Reachable (proj x) y) :
      ∃ z, G.Reachable x z ∧ proj z = y := by
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ⟨x, Reachable.rfl, rfl⟩
    | tail _ edge ih =>
      obtain ⟨z, r, e⟩ := ih
      rcases (shapeDown _ _).mp edge with rfl | rfl
      · exact ⟨p z, r.trans (((shapeUp _ _).mpr (Or.inl rfl)).reachable), (semiP z).trans (congrArg P e)⟩
      · exact ⟨q z, r.trans (((shapeUp _ _).mpr (Or.inr rfl)).reachable), (semiQ z).trans (congrArg Q e)⟩
  let shiftIso (a : A) : G ≃g G := by
    let τ : X ≃ X := {
      toFun := fun y => a • y
      invFun := fun y => a⁻¹ • y
      left_inv := inv_smul_smul a
      right_inv := smul_inv_smul a }
    refine { toEquiv := τ, map_rel_iff' := ?_ }
    intro u v
    rw [shapeUp, shapeUp]
    change (p (a • u) = a • v ∨ q (a • u) = a • v) ↔ _
    rw [presP, presQ]
    exact or_congr τ.injective.eq_iff τ.injective.eq_iff
  have sameSize (y : U) :
      (G.connectedComponentMk y.val).supp.ncard = (G.connectedComponentMk x).supp.ncard := by
    have r : H.Reachable (proj x) (proj y.val) :=
      (ConnectedComponent.eq.mp y.prop).symm
    obtain ⟨z, r', eq⟩ := liftReach _ r
    obtain ⟨a, ha⟩ := (fibre z y.val).mp eq
    have equiv := SimpleGraph.ConnectedComponent.isoEquivSupp (shiftIso a) (G.connectedComponentMk z)
    have counts : (G.connectedComponentMk z).supp.ncard =
        (G.connectedComponentMk (a • z)).supp.ncard := Nat.card_congr equiv
    rw [ha, ← ConnectedComponent.eq.mpr r'] at counts
    exact counts.symm
  let base : U → B := fun u => ⟨proj u.val, u.prop⟩
  have baseFibre (b : B) : Nat.card {u // base u = b} = Nat.card A := by
    have reach : H.Reachable (proj x) b.val := (ConnectedComponent.eq.mp b.prop).symm
    obtain ⟨z, _, eq⟩ := liftReach _ reach
    let toFibre : A → {u // base u = b} := fun a =>
      let same := (fibre z (a • z)).mpr ⟨a, rfl⟩
      let hit := same.symm.trans eq
      ⟨⟨a • z, by change proj (a • z) ∈ B; rw [hit]; exact b.prop⟩, Subtype.ext hit⟩
    have toFibreBijective : Bijective toFibre := by
      constructor
      · intro a c h
        have e : a • z = c • z := congrArg (fun t => t.val.val) h
        have fix : (c⁻¹ * a) • z = z := by rw [mul_smul, e, inv_smul_smul]
        simpa using congrArg (c * ·) (free _ _ fix)
      · intro a
        have projEq : proj a.val.val = b.val := congrArg Subtype.val a.prop
        obtain ⟨c, h⟩ := (fibre z a.val.val).mp (eq.trans projEq.symm)
        exact ⟨c, Subtype.ext (Subtype.ext h)⟩
    exact (Nat.card_congr (Equiv.ofBijective toFibre toFibreBijective)).symm
  let components : U → T := fun u => ⟨G.connectedComponentMk u.val, ⟨u, rfl⟩⟩
  have componentFibre (C : T) :
      Nat.card {u // components u = C} = (G.connectedComponentMk x).supp.ncard := by
    obtain ⟨a, ha⟩ := C.prop
    have subset {y : X} (h : y ∈ C.val.supp) : y ∈ U := by
      have reach : G.Reachable y a.val := ConnectedComponent.eq.mp (h.trans ha.symm)
      exact (ConnectedComponent.eq.mpr (mapReach reach)).trans a.prop
    let eqv : C.val.supp ≃ {u // components u = C} := {
      toFun y := ⟨⟨y.val, subset y.prop⟩, Subtype.ext y.prop⟩
      invFun y := ⟨y.val.val, congrArg Subtype.val y.prop⟩
      left_inv y := Subtype.ext rfl
      right_inv y := Subtype.ext (Subtype.ext rfl) }
    rw [← Nat.card_congr eqv, Nat.card_coe_set_eq, ← ha]
    exact sameSize a
  have n₁ := card_of_equal_fibres base (Nat.card A) baseFibre
  have n₂ := card_of_equal_fibres components ((G.connectedComponentMk x).supp.ncard) componentFibre
  rw [Nat.card_coe_set_eq B] at n₁
  rw [Nat.card_coe_set_eq T, size] at n₂
  have e : B.ncard * (T.ncard * s) = B.ncard * Nat.card A := by
    rw [← Nat.mul_assoc, Nat.mul_comm B.ncard T.ncard, Nat.mul_assoc, ← n₂, n₁]
  exact Nat.eq_of_mul_eq_mul_left (ConnectedComponent.nonempty_supp _).ncard_pos e

private theorem lift_period {A X Y : Type*} [CommGroup A] [MulAction A X]
    (exponentTwo : ∀ a : A, a ^ 2 = 1)
    (free : ∀ (a : A) (x : X), a • x = x → a = 1)
    (project : X → Y) (f : X → X) (g : Y → Y)
    (fiber : ∀ x y, project x = project y ↔ ∃ a : A, a • x = y)
    (equivariant : ∀ (a : A) (x : X), f (a • x) = a • f x)
    (semi : Semiconj project f g) (x : X)
    (_positive : 0 < minimalPeriod g (project x)) :
    let k := minimalPeriod g (project x)
    ∃! a : A, (f^[k]) x = a • x ∧
      (∀ y, project y = project x → (f^[k]) y = a • y) ∧
      (∀ j : ℕ, (f^[j * k]) x = a ^ j • x) ∧
      minimalPeriod f x = k * orderOf a ∧ orderOf a ∣ 2 := by
  let k := minimalPeriod g (project x)
  have injectiveAt (y : X) : Injective (fun a : A => a • y) := by
    intro a b eq
    change a • y = b • y at eq
    have fixes : (b⁻¹ * a) • y = y := by
      rw [mul_smul, eq, inv_smul_smul]
    have unit := free _ _ fixes
    simpa using congrArg (b * ·) unit
  have commutes (a : A) (j : ℕ) (y : X) : (f^[j]) (a • y) = a • (f^[j]) y :=
    ((show Function.Commute f (a • ·) from equivariant a).iterate_left j) y
  have baseFix : (g^[k]) (project x) = project x := isPeriodicPt_minimalPeriod g (project x)
  have projected : project ((f^[k]) x) = project x :=
    (semi.iterate_right k x).trans baseFix
  obtain ⟨a, ha⟩ := (fiber x ((f^[k]) x)).mp projected.symm
  have returns (j : ℕ) : (f^[j * k]) x = a ^ j • x := by
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          (f^[j.succ * k]) x = (f^[k]) ((f^[j * k]) x) := by
            rw [Nat.succ_mul, Nat.add_comm (j * k) k, iterate_add_apply]
          _ = a ^ j • (f^[k]) x := by rw [ih, commutes]
          _ = a ^ j.succ • x := by rw [← ha, pow_succ, mul_smul]
  have upper : minimalPeriod f x ∣ k * orderOf a := by
    apply IsPeriodicPt.minimalPeriod_dvd
    change (f^[k * orderOf a]) x = x
    rw [Nat.mul_comm k, returns, pow_orderOf_eq_one, one_smul]
  have baseDivides : k ∣ minimalPeriod f x :=
    ((isPeriodicPt_minimalPeriod f x).map semi).minimalPeriod_dvd
  obtain ⟨j, hj⟩ := baseDivides
  have fixes : a ^ j • x = x := by
    rw [← returns j, Nat.mul_comm j, ← hj]
    exact isPeriodicPt_minimalPeriod f x
  have orderDivides : orderOf a ∣ j := orderOf_dvd_iff_pow_eq_one.mpr (free _ _ fixes)
  have lower : k * orderOf a ∣ minimalPeriod f x := by
    rw [hj]
    exact Nat.mul_dvd_mul_left k orderDivides
  refine ⟨a, ⟨ha.symm, ?_, returns, Nat.dvd_antisymm upper lower,
    orderOf_dvd_iff_pow_eq_one.mpr (exponentTwo a)⟩, ?_⟩
  · intro y hy
    obtain ⟨b, rfl⟩ := (fiber x y).mp hy.symm
    rw [commutes, ← ha, ← mul_smul, mul_comm b a, mul_smul]
  · intro b hb
    exact injectiveAt x (hb.1.symm.trans ha.symm)

private theorem component_period {X : Type*} [Finite X] (G : SimpleGraph X) (p q : X → X)
    (hp : Involutive p) (hq : Involutive q)
    (noP : ∀ x, p x ≠ x) (noQ : ∀ x, q x ≠ x)
    (edges : ∀ u v, G.Adj u v ↔ p u = v ∨ q u = v) (x : X) :
    (G.connectedComponentMk x).supp.ncard = 2 * minimalPeriod (p ∘ q) x := by
  let s : Equiv.Perm X := ⟨p, p, hp, hp⟩
  let t : Equiv.Perm X := ⟨q, q, hq, hq⟩
  let f := p ∘ q
  let k := minimalPeriod f x
  have hinj : Injective f := hp.injective.comp hq.injective
  have kpos : 0 < k := minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts x)
  have sameEdges : G.Adj = fun u v => p u = v ∨ q u = v := by
    funext u v
    exact propext (edges u v)
  have sameComponent :
      (G.connectedComponentMk x).supp = AlternatingComponentParity.Component s t x := by
    ext y
    rw [ConnectedComponent.mem_supp_iff (G.connectedComponentMk x), ConnectedComponent.eq,
      reachable_comm, reachable_iff_reflTransGen, sameEdges]
    rfl
  have permProduct : (⇑(s * t) : X → X) = f := by
    funext y
    exact Equiv.Perm.mul_apply s t y
  have sameOrbit : InvolutionOrbitSplit.RotationOrbit (s * t) x =
      Set.range (fun n : Fin k => f^[n.val] x) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hy
      refine ⟨⟨n % k, Nat.mod_lt n kpos⟩, ?_⟩
      change f^[n % minimalPeriod f x] x = y
      rw [iterate_mod_minimalPeriod_eq]
      simpa only [Equiv.Perm.coe_pow, permProduct] using hn
    · rintro ⟨n, hn⟩
      refine ⟨(n.val : ℤ), ?_⟩
      rw [zpow_natCast]
      simpa only [Equiv.Perm.coe_pow, permProduct] using hn
  have hcard : (InvolutionOrbitSplit.RotationOrbit (s * t) x).ncard = k := by
    rw [sameOrbit, Set.ncard_range_of_injective]
    · simp
    · intro i j h
      apply Fin.ext
      exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp h
  rw [sameComponent, AlternatingComponentParity.connected_ncard_eq_two_mul s t hp hq noP noQ x,
    hcard]

@[instance_reducible]
private def centreGroup {L : Type*} [Mul L] (e : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) : CommGroup (Set.center L) where
  one := ⟨e, ⟨fun x => comm e x,
    fun x y => by rw [unit, unit],
    fun x y => by rw [comm (x * y) e, unit, comm y e, unit]⟩⟩
  mul a b := ⟨a.val * b.val, Set.mul_mem_center a.prop b.prop⟩
  inv a := a
  mul_assoc a b c := Subtype.ext ((Set.mem_center_iff.mp a.prop).left_assoc b.val c.val).symm
  one_mul a := Subtype.ext (unit a.val)
  mul_one a := Subtype.ext ((comm a.val e).trans (unit a.val))
  inv_mul_cancel a := Subtype.ext (by
    change a.val * a.val = e
    simpa only [comm a.val e, unit] using invol a.val e)
  mul_comm a b := Subtype.ext (comm a.val b.val)

@[instance_reducible]
private def centreAction {L : Type*} [Mul L] (e : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) :
    let _ := centreGroup e unit comm invol
    MulAction (Set.center L) L :=
  let _ := centreGroup e unit comm invol
  { smul := fun z x => z.val * x
    one_smul := unit
    mul_smul := fun a b x => ((Set.mem_center_iff.mp a.prop).left_assoc b.val x).symm }

private def overlay {X : Type*} (P Q : X → X) (pInv : Involutive P) (qInv : Involutive Q)
    (pFree : ∀ x, P x ≠ x) (qFree : ∀ x, Q x ≠ x) : SimpleGraph X where
  Adj x y := P x = y ∨ Q x = y
  symm := ⟨by
    intro a b h
    rcases h with h | h
    · exact Or.inl (h ▸ pInv a)
    · exact Or.inr (h ▸ qInv a)⟩
  loopless := ⟨fun a h => h.elim (pFree a) (qFree a)⟩

private theorem central_quotient_component_size {L : Type*} [Finite L] [Mul L] (e p q : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (pNoncentral : p ∉ Set.center L) (qNoncentral : q ∉ Set.center L)
    (different : ¬ ∃ z ∈ Set.center L, z * q = p)
    (G : SimpleGraph L) (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v) :
    let _ := centreGroup e unit comm invol
    let _ := centreAction e unit comm invol
    let C := Quotient (MulAction.orbitRel (Set.center L) L)
    let proj : L → C := Quotient.mk _
    ∃ (P Q : C → C) (Gbar : SimpleGraph C),
      Semiconj proj (p * ·) P ∧ Semiconj proj (q * ·) Q ∧
      (∀ u v, Gbar.Adj u v ↔ P u = v ∨ Q u = v) ∧
      (∀ b, P b ≠ Q b) ∧
      ∀ x : L, ∃ a : Set.center L,
        ((fun y => p * (q * y))^[minimalPeriod (P ∘ Q) (proj x)]) x = a • x ∧
        (G.connectedComponentMk x).supp.ncard =
          (Gbar.connectedComponentMk (proj x)).supp.ncard * orderOf a ∧
        orderOf a ∣ 2 ∧
        let B := (Gbar.connectedComponentMk (proj x)).supp
        let T := Set.range (fun y : proj ⁻¹' B => G.connectedComponentMk y.val)
        T.ncard * orderOf a = (Set.center L).ncard := by
  classical
  let _ := centreGroup e unit comm invol
  let _ := centreAction e unit comm invol
  let C := Quotient (MulAction.orbitRel (Set.center L) L)
  let proj : L → C := Quotient.mk _
  let _ : Finite C := Finite.of_surjective proj Quotient.mk_surjective
  have cube (x : L) : x * e = x := (comm x e).trans (unit x)
  have centralUnit : e ∈ Set.center L := (1 : Set.center L).prop
  have cancelRight (x : L) : Injective (· * x) := by
    intro a b h
    change a * x = b * x at h
    rw [comm a x, comm b x] at h
    exact (show Involutive (x * ·) from invol x).injective h
  have expTwo (z : Set.center L) : z ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two]
    change z.val * z.val = e
    simpa only [cube] using invol z.val e
  have free (z : Set.center L) (x : L) (h : z • x = x) : z = 1 := by
    apply Subtype.ext
    exact cancelRight x (h.trans (unit x).symm)
  have fibre (x y : L) : proj x = proj y ↔ ∃ z : Set.center L, z • x = y := by
    constructor
    · intro h
      exact MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
    · intro h
      exact (Quotient.sound (MulAction.mem_orbit_iff.mpr h)).symm
  have commutes (r : L) (z : Set.center L) (x : L) :
      r * (z • x) = z • (r * x) :=
    ((Set.mem_center_iff.mp z.prop).left_comm r x).symm
  let lift (r : L) : C → C :=
    Quotient.lift (fun x => proj (r * x)) (by
      intro a b hab
      obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp hab
      symm
      apply (fibre _ _).2
      refine ⟨z, ?_⟩
      exact (commutes r z b).symm.trans (congrArg (r * ·) hz))
  have liftAt (r x : L) : lift r (proj x) = proj (r * x) := rfl
  have liftInv (r : L) : Involutive (lift r) := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x => change lift r (lift r (proj x)) = proj x; rw [liftAt, liftAt, invol]
  have pFree (x : L) : p * x ≠ x := by
    intro h
    exact pNoncentral (cancelRight x (h.trans (unit x).symm) ▸ centralUnit)
  have qFree (x : L) : q * x ≠ x := by
    intro h
    exact qNoncentral (cancelRight x (h.trans (unit x).symm) ▸ centralUnit)
  have downstairsFree (r : L) (nr : r ∉ Set.center L) (x : C) : lift r x ≠ x := by
    induction x using Quotient.inductionOn with
    | _ x =>
        change lift r (proj x) ≠ proj x
        rw [liftAt]
        intro h
        obtain ⟨z, hz⟩ := (fibre x (r * x)).mp h.symm
        have eq : z.val = r := cancelRight x hz
        exact nr (eq ▸ z.prop)
  have downstairsDistinct (x : C) : lift p x ≠ lift q x := by
    induction x using Quotient.inductionOn with
    | _ x =>
        change lift p (proj x) ≠ lift q (proj x)
        rw [liftAt, liftAt]
        intro eq
        obtain ⟨z, hz⟩ := (fibre (q * x) (p * x)).mp eq.symm
        change z.val * (q * x) = p * x at hz
        rw [(Set.mem_center_iff.mp z.prop).left_assoc] at hz
        exact different ⟨z.val, z.prop, cancelRight x hz⟩
  let H := overlay (lift p) (lift q) (liftInv p) (liftInv q)
    (downstairsFree p pNoncentral) (downstairsFree q qNoncentral)
  have semi : Semiconj proj (fun x => p * (q * x)) (lift p ∘ lift q) := by
    intro x
    change proj (p * (q * x)) = lift p (lift q (proj x))
    rw [liftAt, liftAt]
  refine ⟨lift p, lift q, H, fun x => (liftAt p x).symm, fun x => (liftAt q x).symm,
    fun _ _ => Iff.rfl, downstairsDistinct, fun x => ?_⟩
  have fEq (z : Set.center L) (y : L) :
      p * (q * (z • y)) = z • (p * (q * y)) := by rw [commutes q, commutes p]
  have gInj : Injective (lift p ∘ lift q) := (liftInv p).injective.comp (liftInv q).injective
  have gPos : 0 < minimalPeriod (lift p ∘ lift q) (proj x) :=
    minimalPeriod_pos_of_mem_periodicPts (gInj.mem_periodicPts _)
  obtain ⟨a, ⟨ret, _, _, period, order⟩, _⟩ :=
    lift_period expTwo free proj (fun x => p * (q * x))
      (lift p ∘ lift q) fibre fEq semi x gPos
  have sizeUp := component_period G (p * ·) (q * ·)
    (invol p) (invol q) pFree qFree edges x
  have sizeDown := component_period H (lift p) (lift q)
    (liftInv p) (liftInv q) (downstairsFree p pNoncentral) (downstairsFree q qNoncentral)
    (fun _ _ => Iff.rfl) (proj x)
  have componentSize :
      (G.connectedComponentMk x).supp.ncard =
      (H.connectedComponentMk (proj x)).supp.ncard * orderOf a := by
    rw [sizeUp, sizeDown, Nat.mul_assoc]
    exact congrArg (2 * ·) period
  refine ⟨a, ret, componentSize, order, ?_⟩
  exact component_count_factor G H proj
    (p * ·) (q * ·) (lift p) (lift q) edges (fun _ _ => Iff.rfl)
    (fun y => (liftAt p y).symm) (fun y => (liftAt q y).symm)
    (commutes p) (commutes q) fibre free x (orderOf a) componentSize

open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered)
open SteinerAlternatingSwitches (pivotGraph)
open SteinerMatchingTranslations (translate_involutive)
open SteinerSwitchCentre (steinerMul product_comm)

/-- For distinct nonidentity quotient pivots, the alternating components
    over a given quotient component have the two possible lifting sizes. -/
theorem point_deleted_component_lifts {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) (v : Fin r) :
    let _ := steinerMul valid complete
    let p : Option (Fin (r + 1)) := some q
    let u : Option (Fin (r + 1)) := some (q.succAbove v)
    let Z := Set.center (Option (Fin (r + 1)))
    p ∉ Z → u ∉ Z → (¬ ∃ z ∈ Z, z * u = p) →
    ∃ (B : Type) (proj : Option (Fin (r + 1)) → B) (P Q : B → B)
      (H : SimpleGraph B),
      Surjective proj ∧
      (∀ x y, proj x = proj y ↔ ∃ z ∈ Z, z * x = y) ∧
      Semiconj proj ((some q : Option (Fin (r + 1))) * ·) P ∧ Semiconj proj (u * ·) Q ∧
      (∀ x y, H.Adj x y ↔ P x = y ∨ Q x = y) ∧
      (∀ b, P b ≠ Q b) ∧
      ∀ x : Option (Fin (r + 1)), ∃ a ∈ Z,
        let k := minimalPeriod (P ∘ Q) (proj x)
        let d : ℕ := if a = none then 1 else 2
        let G := pivotGraph valid complete q v
        let C := (H.connectedComponentMk (proj x)).supp
        let T := Set.range (fun y : proj ⁻¹' C => G.connectedComponentMk y.val)
        ((fun y => p * (u * y))^[k]) x = a * x ∧
        (G.connectedComponentMk x).supp.ncard = C.ncard * d ∧
        T.ncard * d = Z.ncard := by
  classical
  dsimp only
  let _ := steinerMul valid complete
  let p : Option (Fin (r + 1)) := some q
  let u : Option (Fin (r + 1)) := some (q.succAbove v)
  intro pNoncentral uNoncentral different
  have unit (x : Option (Fin (r + 1))) : none * x = x := rfl
  have comm (x y : Option (Fin (r + 1))) : x * y = y * x :=
    product_comm valid complete x y
  have invol (x y : Option (Fin (r + 1))) : x * (x * y) = y := by
    cases x with
    | none => rfl
    | some x => exact translate_involutive valid complete x y
  let Z := Set.center (Option (Fin (r + 1)))
  let _ := centreGroup none unit comm invol
  let _ := centreAction none unit comm invol
  let B := Quotient (MulAction.orbitRel Z (Option (Fin (r + 1))))
  let proj : Option (Fin (r + 1)) → B := Quotient.mk _
  obtain ⟨P, Q, H, semiP, semiQ, edges, distinct, lift⟩ :=
    central_quotient_component_size none p u unit comm invol pNoncentral uNoncentral
      different (pivotGraph valid complete q v) (fun _ _ => Iff.rfl)
  refine ⟨B, proj, P, Q, H, Quotient.mk_surjective, ?_, semiP, semiQ, edges, distinct, ?_⟩
  · intro x y
    constructor
    · intro h
      obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h.symm)
      exact ⟨z.val, z.prop, hz⟩
    · rintro ⟨z, hz, eq⟩
      exact (Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨⟨z, hz⟩, eq⟩)).symm
  · intro x
    obtain ⟨a, ret, sizes, divides, count⟩ := lift x
    have order : orderOf a = (if a.val = none then (1 : ℕ) else 2) := by
      by_cases h : a.val = none
      · have eq : a = 1 := Subtype.ext h
        rw [if_pos h, eq, orderOf_one]
      · have notOne : orderOf a ≠ 1 := by
          intro eq
          exact h (congrArg Subtype.val (orderOf_eq_one_iff.mp eq))
        have eq := (Nat.dvd_prime Nat.prime_two).mp divides |>.resolve_left notOne
        simp [h, eq]
    refine ⟨a.val, a.prop, ret, ?_, ?_⟩
    · rw [← order]
      exact sizes
    · rw [← order]
      exact count

end D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient
