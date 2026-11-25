/- GID: D5/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Use exact cyclic integration to identify literal ribbon boundary cycles with binary interlacement nullity. -/

import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank

section BouquetRankBridge
open LinearMap Submodule

section Pairing
variable {F X W : Type*} [Field F]
  [AddCommGroup X] [Module F X] [FiniteDimensional F X]
  [AddCommGroup W] [Module F W]

/-- Pulling an intersection pairing back along a surjection onto its
homology image does not change rank, even if many cycles vanish there. -/
theorem pullback_pairing_rank (A : X →ₗ[F] W) (hA : Function.Surjective A)
    (B : W →ₗ[F] Module.Dual F W) :
    Module.finrank F (B.compl₁₂ A A).range = Module.finrank F B.range := by
  have htop : range A = ⊤ := LinearMap.range_eq_top.mpr hA
  have hr : range (B.comp A) = range B := LinearMap.range_comp_of_range_eq_top B htop
  have hd := LinearMap.dualMap_injective_of_surjective hA
  let P := A.dualMap.comp (B.comp A)
  have he : ker P = ker (B.comp A) := by
    ext x
    change A.dualMap ((B.comp A) x) = 0 ↔ (B.comp A) x = 0
    rw [← map_zero A.dualMap]
    exact hd.eq_iff
  have h₁ := finrank_range_add_finrank_ker P
  have h₂ := finrank_range_add_finrank_ker (B.comp A)
  rw [he] at h₁
  rw [hr] at h₂
  change Module.finrank F P.range = _
  omega
end Pairing

section Cycles
variable {F D : Type*} [Field F] [Finite D]

/-- Binary or field-valued boundary cochains are exactly quotient
functions on the permutation's actual boundary cycles. -/
def boundaryConstant (p : Equiv.Perm D) : Submodule F (D → F) where
  carrier := { x | ∀ i j, p.SameCycle i j → x i=x j }
  zero_mem' := by
    change ∀ i j, p.SameCycle i j → (0 : F) = 0
    intro i j h; rfl
  add_mem' := by
    intro x y hx hy i j h
    change x i+y i=x j+y j
    rw [hx i j h,hy i j h]
  smul_mem' := by
    intro a x hx i j h
    change a*x i=a*x j
    rw [hx i j h]

def boundaryConstantEquiv (p : Equiv.Perm D) :
    boundaryConstant (F:=F) p ≃ₗ[F] (Quotient (Equiv.Perm.SameCycle.setoid p) → F) where
  toFun x := Quotient.lift x.val (fun i j h => x.prop i j h)
  invFun g := ⟨fun i => g (Quotient.mk _ i), fun _ _ h => congrArg g (Quotient.sound h)⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by
    intro g
    funext v
    obtain ⟨i,rfl⟩ := Quotient.exists_rep v
    rfl
  map_add' := by
    intro x y
    funext v
    obtain ⟨i,rfl⟩ := Quotient.exists_rep v
    rfl
  map_smul' := by
    intro a x
    funext v
    obtain ⟨i,rfl⟩ := Quotient.exists_rep v
    rfl

theorem boundary_cycle_count_is_finrank (p : Equiv.Perm D) :
    Module.finrank F (boundaryConstant (F:=F) p) = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) := by
  classical
  let _ := Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))
  rw [(boundaryConstantEquiv (F:=F) p).finrank_eq,Module.finrank_fintype_fun_eq_card,Nat.card_eq_fintype_card]
end Cycles
end BouquetRankBridge

section CyclicDifference
open Finset
open scoped BigOperators

variable {F : Type*} [AddCommGroup F]

def wrap (n k : ℕ) : Fin (n+1) := ⟨k%(n+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
def cyclicNext {n : ℕ} (i : Fin (n+1)) : Fin (n+1) := wrap n (i.val+1)

def cyclicPrefix {n : ℕ} (g : Fin (n+1) → F) (k : ℕ) : F :=
  ∑ i ∈ range k, g (wrap n i)

private theorem prefix_step {n : ℕ} (g : Fin (n+1) → F) (k : ℕ) :
    cyclicPrefix g (k+1)=cyclicPrefix g k + g (wrap n k) := by
  exact sum_range_succ _ k

@[simp] theorem wrap_val {n : ℕ} (i : Fin (n+1)) : wrap n i.val=i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- On the finite cyclic dart carrier, sum-zero increments have an exact
primitive given by prefix sums and an arbitrary initial value. -/
theorem cyclic_prefix_primitive {n : ℕ} (g : Fin (n+1) → F)
    (hg : cyclicPrefix g (n+1)=0) (a : F) (i : Fin (n+1)) :
    (a+cyclicPrefix g (cyclicNext i).val)-(a+cyclicPrefix g i.val)=g i := by
  have he := prefix_step g i.val
  rw [wrap_val] at he
  by_cases h : i.val+1<n+1
  · have hn : (cyclicNext i).val=i.val+1 := Nat.mod_eq_of_lt h
    rw [hn,he]
    abel
  · have ht : i.val+1=n+1 := by omega
    have hn : (cyclicNext i).val=0 := by
      change (i.val+1)%(n+1)=0
      rw [ht,Nat.mod_self]
    rw [ht,hg] at he
    rw [hn]
    have hz : cyclicPrefix g 0=0 := rfl
    rw [hz]
    rw [← sub_eq_of_eq_add (a:=0) he]
    abel

/-- No extra information survives the cyclic derivative except the single
basepoint value. This recovers every cochain satisfying a prescribed increment. -/
theorem cyclic_prefix_recovers {n : ℕ} (f g : Fin (n+1) → F)
    (hd : ∀ i, f (cyclicNext i)-f i=g i) (i : Fin (n+1)) :
    f i=f 0+cyclicPrefix g i.val := by
  suffices h : ∀ k : ℕ, ∀ hk : k<n+1,
      f (⟨k,hk⟩ : Fin (n+1))=f 0+cyclicPrefix g k by exact h i.val i.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    change f 0=f 0+cyclicPrefix g 0
    simp [cyclicPrefix]
  | succ k ih =>
    intro hk
    have hk' : k<n+1 := by omega
    let j : Fin (n+1) := ⟨k,hk'⟩
    have hn : cyclicNext j=⟨k+1,hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
    have hr := hd j
    rw [hn] at hr
    rw [eq_add_of_sub_eq hr,ih hk',prefix_step g]
    have he : wrap n k=j := Fin.ext (Nat.mod_eq_of_lt hk')
    rw [he]
    abel
end CyclicDifference

section CyclicBoundaryEquiv
open LinearMap Submodule Finset
open scoped BigOperators

variable {F Y : Type*} [Field F] [AddCommGroup Y] [Module F Y]

def prefixLinear (n : ℕ) : (Fin (n+1) → F) →ₗ[F] (Fin (n+1) → F) where
  toFun g i := cyclicPrefix g i.val
  map_add' := by intro g h; funext i; simp [cyclicPrefix,Finset.sum_add_distrib]
  map_smul' := by intro a g; funext i; simp [cyclicPrefix,Finset.mul_sum]

def endpointDebt {n : ℕ} (lift : Y →ₗ[F] (Fin (n+1)→F))
    (read : (Fin (n+1)→F) →ₗ[F] Y) : Y →ₗ[F] Y :=
  read.comp ((prefixLinear n).comp lift) - LinearMap.id

/-- One primitive constant and one compatible endpoint vector determine
an actual boundary cochain uniquely. The local switching statement and
cyclic closure are the only combinatorial inputs. -/
def boundaryEndpointEquiv {n : ℕ} (p : Equiv.Perm (Fin (n+1)))
    (lift : Y →ₗ[F] (Fin (n+1)→F)) (read : (Fin (n+1)→F) →ₗ[F] Y)
    (hshift : ∀ a : F, ∀ f, read (fun i => a+f i)=read f)
    (hclose : ∀ z, cyclicPrefix (lift z) (n+1)=0)
    (hstep : ∀ f, f ∈ boundaryConstant (F:=F) p ↔
      ∀ i, f (cyclicNext i)-f i = lift (read f) i) :
    boundaryConstant (F:=F) p ≃ₗ[F] F × (endpointDebt lift read).ker where
  toFun x := ⟨x.val 0,⟨read x.val,by
    have he := cyclic_prefix_recovers x.val (lift (read x.val)) ((hstep _).mp x.prop)
    change read (prefixLinear n (lift (read x.val)))-read x.val=0
    apply sub_eq_zero.mpr
    have hr := congrArg read (funext he)
    rw [hshift] at hr
    exact hr.symm⟩⟩
  invFun y := ⟨fun i => y.1+prefixLinear n (lift y.2.val) i,by
    have hy : read (prefixLinear n (lift y.2.val))=y.2.val := by
      apply sub_eq_zero.mp
      exact y.2.prop
    apply (hstep _).mpr
    rw [hshift,hy]
    exact cyclic_prefix_primitive (lift y.2.val) (hclose y.2.val) y.1⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    exact (cyclic_prefix_recovers x.val (lift (read x.val)) ((hstep _).mp x.prop) i).symm
  right_inv := by
    intro y
    apply Prod.ext
    · change y.1+cyclicPrefix (lift y.2.val) 0=y.1
      simp [cyclicPrefix]
    · apply Subtype.ext
      change read (fun i => y.1+prefixLinear n (lift y.2.val) i)=y.2.val
      rw [hshift]
      exact sub_eq_zero.mp y.2.prop
  map_add' := by
    intro x y
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact map_add read x.val y.val
  map_smul' := by
    intro a x
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact map_smul read a x.val

theorem boundary_count_plus_debt_rank {n : ℕ} [FiniteDimensional F Y]
    (p : Equiv.Perm (Fin (n+1))) (lift : Y →ₗ[F] (Fin (n+1)→F))
    (read : (Fin (n+1)→F) →ₗ[F] Y)
    (hshift : ∀ a : F, ∀ f, read (fun i => a+f i)=read f)
    (hclose : ∀ z, cyclicPrefix (lift z) (n+1)=0)
    (hstep : ∀ f, f ∈ boundaryConstant (F:=F) p ↔
      ∀ i, f (cyclicNext i)-f i = lift (read f) i) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) +
      Module.finrank F (endpointDebt lift read).range = 1+Module.finrank F Y := by
  have he := (boundaryEndpointEquiv p lift read hshift hclose hstep).finrank_eq
  rw [boundary_cycle_count_is_finrank,Module.finrank_prod,Module.finrank_self] at he
  have hk := LinearMap.finrank_range_add_finrank_ker (endpointDebt lift read)
  omega
end CyclicBoundaryEquiv

section LiteralBouquetCochains
open Finset LinearMap Submodule
open scoped BigOperators

variable {F E D : Type*} [Field F] [Fintype E] [DecidableEq D]

def pairedRead (a b : E → D) : (D→F) →ₗ[F] (E→F) :=
  { toFun := fun f e => f (b e)-f (a e)
    map_add' := by intro f g; funext e; change (f (b e)+g (b e))-(f (a e)+g (a e)) = _; simp only [Pi.add_apply]; abel
    map_smul' := by intro c f; funext e; change c*f (b e)-c*f (a e)=c*(f (b e)-f (a e)); ring }

def pairedLift (a b : E → D) : (E→F) →ₗ[F] (D→F) :=
  LinearMap.pi fun i =>
    (∑ e : E, if a e=i then LinearMap.proj e else 0) -
      (∑ e : E, if b e=i then LinearMap.proj e else 0)

omit [Fintype E] [DecidableEq D] in
@[simp] theorem pairedRead_apply (a b : E → D) (f : D→F) (e : E) :
    pairedRead a b f e=f (b e)-f (a e) := rfl

theorem pairedLift_apply (a b : E → D) (z : E→F) (i : D) :
    pairedLift a b z i = (∑ e : E, if a e=i then z e else 0) -
      (∑ e : E, if b e=i then z e else 0) := by
  simp [pairedLift,LinearMap.sum_apply]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _ <;> split <;> rfl

omit [Fintype E] [DecidableEq D] in
theorem pairedRead_shift (a b : E→D) (c : F) (f : D→F) :
    pairedRead a b (fun i => c+f i)=pairedRead a b f := by
  funext e
  simp

private theorem sum_port_present {a : E→D} (ha : Function.Injective a) (z : E→F) (e : E) :
    (∑ j : E, if a j=a e then z j else 0)=z e := by
  classical
  simp [ha.eq_iff]

private theorem sum_port_absent {a : E→D} (z : E→F) {i : D} (h : ∀ e, a e≠i) :
    (∑ j : E, if a j=i then z j else 0)=0 := by simp [h]

/-- A concrete pair switch on disjoint ports gives exactly the oriented
difference at the ports and no difference at all on untouched darts. -/
theorem paired_switch_delta (a b : E→D) (alpha : Equiv.Perm D)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ e j, a e≠b j)
    (hsa : ∀ e, alpha (a e)=b e) (hsb : ∀ e, alpha (b e)=a e)
    (hfix : ∀ i, (∀ e, a e≠i) → (∀ e, b e≠i) → alpha i=i)
    (f : D→F) (i : D) :
    pairedLift a b (pairedRead a b f) i=f (alpha i)-f i := by
  classical
  rw [pairedLift_apply]
  by_cases hA : ∃ e, a e=i
  · obtain ⟨e,rfl⟩ := hA
    rw [sum_port_present ha, sum_port_absent _ (fun j h => hd e j h.symm),sub_zero,hsa]
    rfl
  · push Not at hA
    by_cases hB : ∃ e, b e=i
    · obtain ⟨e,rfl⟩ := hB
      rw [sum_port_absent _ hA, sum_port_present hb, hsb,pairedRead_apply]
      abel
    · push Not at hB
      rw [sum_port_absent _ hA, sum_port_absent _ hB,hfix _ hA hB,sub_self,sub_self]

omit [Fintype E] [DecidableEq D] in
private theorem perm_cochain_iff [Finite D] (p : Equiv.Perm D) (f : D→F) :
    f ∈ boundaryConstant (F:=F) p ↔ ∀ i, f (p i)=f i := by
  change (∀ i j, p.SameCycle i j → f i=f j) ↔ _
  constructor
  · intro h i
    exact (h i (p i) ⟨1,by simp⟩).symm
  · intro h i j hj
    obtain ⟨k,hk⟩ := hj.exists_nat_pow_eq
    subst j
    clear hj
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',Equiv.Perm.mul_apply,h,←ih]

section Cyclic

variable {n : ℕ}
private theorem all_darts_prefix (g : Fin (n+1)→F) :
    cyclicPrefix g (n+1) = ∑ i : Fin (n+1), g i := by
  calc
    cyclicPrefix g (n+1) = ∑ i : Fin (n+1), g (wrap n i.val) :=
      (Fin.sum_univ_eq_sum_range (fun k => g (wrap n k)) (n+1)).symm
    _ = _ := by simp

/-- Each oriented chord contributes plus and minus once, so the cyclic
primitive exists with no compatibility constraint other than endpoint debt. -/
theorem paired_sum_zero (a b : E→Fin (n+1)) (z : E→F) :
    cyclicPrefix (pairedLift a b z) (n+1)=0 := by
  rw [all_darts_prefix]
  simp_rw [pairedLift_apply,sum_sub_distrib]
  rw [sum_comm]
  have hx (c : E→Fin (n+1)) :
      (∑ e : E, ∑ i : Fin (n+1), if c e=i then z e else 0)=∑ e : E, z e := by
    apply sum_congr rfl
    intro e _
    rw [sum_eq_single (c e)]
    · simp
    · intro i _ h; simp [Ne.symm h]
    · simp
  rw [sum_comm (s := (univ : Finset (Fin (n+1)))) (t := (univ : Finset E)),hx,hx,sub_self]

set_option maxHeartbeats 800000 in
/-- Literal boundary circle count of a one-vertex ribbon from disjoint
chord-port switches. No algebraic boundary-count premise is used. -/
theorem literal_bouquet_boundary_rank (sigma alpha : Equiv.Perm (Fin (n+1)))
    (hsigma : ∀ i, sigma i=cyclicNext i)
    (ha2 : Function.Involutive alpha)
    (a b : E→Fin (n+1)) (ha : Function.Injective a) (hb : Function.Injective b)
    (hd : ∀ e j, a e≠b j) (hsa : ∀ e, alpha (a e)=b e) (hsb : ∀ e, alpha (b e)=a e)
    (hfix : ∀ i, (∀ e, a e≠i) → (∀ e, b e≠i) → alpha i=i) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (sigma*alpha))) +
      Module.finrank F (endpointDebt (n:=n) (F:=F) (Y:=E→F) (pairedLift a b) (pairedRead a b)).range =
      1+Fintype.card E := by
  classical
  have hs (f : Fin (n+1)→F) :
      f ∈ boundaryConstant (F:=F) (sigma*alpha) ↔
        ∀ i, f (cyclicNext i)-f i=pairedLift a b (pairedRead a b f) i := by
    rw [perm_cochain_iff]
    simp_rw [paired_switch_delta a b alpha ha hb hd hsa hsb hfix,sub_left_inj]
    constructor
    · intro h i
      have he := h (alpha i)
      rwa [Equiv.Perm.mul_apply,ha2,hsigma] at he
    · intro h i
      rw [Equiv.Perm.mul_apply,hsigma,h,ha2]
  rw [← Module.finrank_fintype_fun_eq_card (R:=F) (η:=E)]
  exact boundary_count_plus_debt_rank (F:=F) (Y:=E→F) (n:=n) (sigma*alpha) (pairedLift a b) (pairedRead a b)
    (pairedRead_shift a b) (paired_sum_zero a b) hs

end Cyclic
end LiteralBouquetCochains

section BouquetInterlace
open Finset LinearMap Submodule
open scoped BigOperators Classical

variable {n : ℕ} {E : Type*} [Fintype E]

private theorem prefix_port_sum {F : Type*} [Field F] (c : Fin (n+1)) (z : F) (k : ℕ)
    (hk : k≤n+1) :
    (∑ i ∈ range k, if c=wrap n i then z else 0)= if c.val<k then z else 0 := by
  calc
    _ = ∑ i ∈ range k, if c.val=i then z else 0 := by
      apply sum_congr rfl
      intro i hi
      have hn : i<n+1 := lt_of_lt_of_le (mem_range.mp hi) hk
      have he : c=wrap n i ↔ c.val=i := by
        rw [Fin.ext_iff]
        change c.val=i%(n+1) ↔ c.val=i
        rw [Nat.mod_eq_of_lt hn]
      simp [he]
    _ = _ := by simp [mem_range]

private theorem paired_prefix {F : Type*} [Field F]
    (a b : E→Fin (n+1)) (z : E→F) (k : ℕ) (hk : k≤n+1) :
    cyclicPrefix (pairedLift a b z) k =
      (∑ e : E, if (a e).val<k then z e else 0) -
      (∑ e : E, if (b e).val<k then z e else 0) := by
  unfold cyclicPrefix
  simp_rw [pairedLift_apply,sum_sub_distrib]
  rw [sum_comm]
  have hx (c : E→Fin (n+1)) : (∑ e : E, ∑ i ∈ range k, if c e=wrap n i then z e else 0) =
      ∑ e : E, if (c e).val<k then z e else 0 :=
    sum_congr rfl (fun e _ => prefix_port_sum (c e) (z e) k hk)
  rw [sum_comm (s := range k) (t := (univ : Finset E)),hx,hx]

def between (l h x : Fin (n+1)) : Prop := l.val≤x.val ∧ x.val<h.val
instance (l h x : Fin (n+1)) : Decidable (between l h x) := by unfold between; infer_instance

private theorem interval_sub {F : Type*} [Field F] (l h x : Fin (n+1))
    (ho : l.val≤h.val) (z : F) :
    (if x.val<h.val then z else 0) - (if x.val<l.val then z else 0) =
      if between l h x then z else 0 := by
  unfold between
  by_cases hl : x.val<l.val
  · have hh : x.val<h.val := lt_of_lt_of_le hl ho
    have hn : ¬l.val≤x.val := not_le.mpr hl
    simp [hl,hh,hn]
  · have hl' : l.val≤x.val := by omega
    by_cases hh : x.val<h.val <;> simp [hl,hl',hh]

private theorem debt_rows {F : Type*} [Field F] (a b : E→Fin (n+1))
    (hord : ∀ e, (a e).val < (b e).val) (z : E→F) (e : E) :
    endpointDebt (n:=n) (pairedLift a b) (pairedRead a b) z e =
      ((∑ j : E, if between (a e) (b e) (a j) then z j else 0) -
       (∑ j : E, if between (a e) (b e) (b j) then z j else 0)) - z e := by
  change cyclicPrefix (pairedLift a b z) (b e).val -
    cyclicPrefix (pairedLift a b z) (a e).val - z e = _
  rw [paired_prefix _ _ _ _ (Nat.le_of_lt (b e).isLt),
      paired_prefix _ _ _ _ (Nat.le_of_lt (a e).isLt)]
  have hx (c : E→Fin (n+1)) :
      (∑ j : E, if (c j).val<(b e).val then z j else 0) -
        (∑ j : E, if (c j).val<(a e).val then z j else 0) =
      ∑ j : E, if between (a e) (b e) (c j) then z j else 0 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun j _ => interval_sub _ _ _ (hord e).le _)
  rw [← hx a,← hx b]
  abel

/-- Endpoints alternate iff the two half-open interval memberships differ.
For off-diagonal chord pairs with disjoint ports the half-open convention
agrees with strict alternation. The diagonal is removed explicitly. -/
def interlaces (a b : E→Fin (n+1)) (e j : E) : Prop :=
  e≠j ∧ (between (a e) (b e) (a j) ↔ ¬ between (a e) (b e) (b j))

/-- The literal endpoint-debt map is the actual binary interlacement
matrix acting on chord coefficients, not an independently chosen matrix. -/
theorem endpoint_debt_is_interlacement (a b : E→Fin (n+1))
    (hord : ∀ e, (a e).val < (b e).val) (z : E→(ZMod 2)) (e : E) :
    endpointDebt (n:=n) (pairedLift a b) (pairedRead a b) z e =
      ∑ j : E, if interlaces a b e j then z j else 0 := by
  classical
  rw [debt_rows a b hord z e, ← sum_sub_distrib]
  have hs : (∑ j : E, if j=e then z j else 0)=z e := by simp
  rw [← hs,← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases he : j=e
  · subst j
    simp [interlaces,between,hord]
  · have he' : e≠j := Ne.symm he
    have hneg : -z j=z j := ZMod.neg_eq_self_mod_two (z j)
    unfold interlaces
    by_cases ha : between (a e) (b e) (a j) <;>
      by_cases hb : between (a e) (b e) (b j) <;>
      simp [ha,hb,he,he',hneg]

noncomputable def interlacementMap (a b : E→Fin (n+1)) : (E→(ZMod 2)) →ₗ[(ZMod 2)] (E→(ZMod 2)) := by
  classical
  exact LinearMap.pi (fun e => ∑ j : E,
    if interlaces a b e j then (LinearMap.proj j : (E→(ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)) else 0)

theorem interlacementMap_apply (a b : E→Fin (n+1)) (z : E→(ZMod 2)) (e : E) :
    interlacementMap a b z e = ∑ j : E, if interlaces a b e j then z j else 0 := by
  classical
  simp [interlacementMap,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split <;> rfl

/-- The native binary Cohn–Lempel equality for an oriented one-vertex
ribbon: boundary circles plus the rank of its interlacement matrix is
one plus the number of retained chords. -/
theorem literal_bouquet_boundary_interlace (sigma alpha : Equiv.Perm (Fin (n+1)))
    (hsigma : ∀ i, sigma i=cyclicNext i)
    (ha2 : Function.Involutive alpha)
    (a b : E→Fin (n+1)) (ha : Function.Injective a) (hb : Function.Injective b)
    (hd : ∀ e j, a e≠b j) (hsa : ∀ e, alpha (a e)=b e) (hsb : ∀ e, alpha (b e)=a e)
    (hfix : ∀ i, (∀ e, a e≠i) → (∀ e, b e≠i) → alpha i=i)
    (hord : ∀ e, (a e).val < (b e).val) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (sigma*alpha))) +
      Module.finrank (ZMod 2) (interlacementMap a b).range =
      1+Fintype.card E := by
  have heq : endpointDebt (n:=n) (F:=(ZMod 2)) (Y:=E→(ZMod 2)) (pairedLift a b) (pairedRead a b) =
      interlacementMap a b := by
    apply LinearMap.ext
    intro z
    funext e
    rw [endpoint_debt_is_interlacement a b hord,interlacementMap_apply]
  rw [← heq]
  exact literal_bouquet_boundary_rank (F:=(ZMod 2)) sigma alpha hsigma ha2 a b ha hb hd hsa hsb hfix
end BouquetInterlace

end D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
