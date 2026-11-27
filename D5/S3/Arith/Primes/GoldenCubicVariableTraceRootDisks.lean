/- GID: D5/S3/Arith/Primes/GoldenCubicVariableTraceRootDisks
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicVariableTraceRootDisks
   mirror-E: none(waiver:proved-variable-seed-root-frontier)
   anchors: []
   utility: none
   digest: The golden variable-seed block has primitive signed traces and exact same-prime root disks; its seed-one readout uses the discriminant-five Lucas instance. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000


namespace D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks
open D5.S1.Scale

/-- One signed Lucas tripling step, with arbitrary starting trace. -/
private def step {R : Type*} [CommRing R] (x : R) : R := x^3 + 3*x

/-- Iterated Lucas trace with free initial seed. -/
private def trace {R : Type*} [CommRing R] : ℕ → R → R
  | 0,x => x
  | j+1,x => step (trace j x)

/-- The variable-seed cubic block. Seed one is the native Lucas block. -/
private def block {R : Type*} [CommRing R] (j : ℕ) (x : R) : R := (trace j x)^2+3

private lemma trace_unit {R : Type*} [CommRing R] (u : Rˣ) (j : ℕ) :
    trace j ((u:R) - ((u⁻¹ : Rˣ):R)) =
      ((u^3^j : Rˣ):R)-(((u⁻¹)^3^j : Rˣ):R) := by
  induction j with
  | zero => simp [trace]
  | succ j ih =>
    simp only [trace, ih, step, pow_succ (3:ℕ), pow_mul, Units.val_pow_eq_pow_val]
    let z : R := (u:R)^3^j
    let w : R := ((u⁻¹:Rˣ):R)^3^j
    change (z-w)^3+3*(z-w)=z^3-w^3
    have hzw : z*w = 1 := by
      dsimp [z,w]
      rw [← mul_pow]
      simp
    linear_combination -3*(z-w)*(hzw)

/-- Denominator-free cyclotomic relation valid over arbitrary commutative
rings and invertible Laurent parameters. -/
private theorem laurent_block {R : Type*} [CommRing R] (u : Rˣ) (j : ℕ) :
    (((u^2)^3^j:Rˣ):R) * block j ((u:R)-((u⁻¹:Rˣ):R)) =
      (((u^2)^3^j:Rˣ):R)^2 + (((u^2)^3^j:Rˣ):R) + 1 := by
  have hc : (((u^2)^3^j:Rˣ):R) = ((u:R)^3^j)^2 := by
    simp only [Units.val_pow_eq_pow_val]
    rw [←pow_mul (u:R) 2 (3^j),Nat.mul_comm 2,pow_mul]
  rw [block,trace_unit,hc]
  let z : R := (u:R)^3^j
  let w : R := ((u⁻¹:Rˣ):R)^3^j
  change z^2*((z-w)^2+3)= (z^2)^2+z^2+1
  have hzw : z*w=1 := by
    dsimp [z,w]
    rw [←mul_pow]
    simp
  linear_combination (z*w+1-2*z^2)*hzw

/-- Exact root criterion in any field of characteristic different from 3.
The input is the signed trace of a nonzero Laurent parameter. -/
private theorem block_zero_iff_primitive {K : Type*} [Field K] (h3 : (3:K)≠0)
    (u : Kˣ) (j : ℕ) :
    block j ((u:K)-((u⁻¹:Kˣ):K)) = 0 ↔ orderOf (u^2) = 3^(j+1) := by
  let v : Kˣ := (u^2)^3^j
  have hval : (v:K) * block j ((u:K)-((u⁻¹:Kˣ):K)) =
      (v:K)^2+(v:K)+1 := laurent_block u j
  have heq : block j ((u:K)-((u⁻¹:Kˣ):K)) = 0 ↔ (v:K)^2+(v:K)+1=0 := by
    rw [←hval, mul_eq_zero]
    simp [Units.ne_zero v]
  rw [heq]
  constructor
  · intro h
    have hv : v≠1 := by
      intro e
      rw [e] at h
      norm_num at h
      exact h3 h
    have hc : (v:K)^3=1 := by
      linear_combination ((v:K)-1)*h
    have huv : (u^2)^3^(j+1)=1 := by
      rw [pow_succ (3:ℕ), pow_mul]
      apply Units.ext
      simpa [v] using hc
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact orderOf_eq_prime_pow hv huv
  · intro h
    have huv : (u^2)^3^(j+1)=1 := h ▸ pow_orderOf_eq_one (u^2)
    have hc : (v:K)^3=1 := by
      change (((u^2)^3^j:Kˣ):K)^3=1
      rw [←Units.val_pow_eq_pow_val, ← pow_mul, ←pow_succ (3:ℕ),huv]
      rfl
    have hv : (v:K)≠1 := by
      intro e
      have he : (u^2)^3^j = 1 := Units.ext e
      have hd : 3^(j+1) ∣ 3^j := h ▸ orderOf_dvd_of_pow_eq_one he
      have hp : 0 < (3:ℕ)^j := by positivity
      have hf := Nat.le_of_dvd hp hd
      rw [pow_succ] at hf
      omega
    have hh : ((v:K)-1)*((v:K)^2+(v:K)+1)=0 := by linear_combination hc
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hv)



/-- Exact divided difference of the iterated trace; no division is used. -/
private def traceSlope {R : Type*} [CommRing R] : ℕ → R → R → R
  | 0,_,_ => 1
  | j+1,x,y =>
    let a := trace j x
    let b := trace j y
    (a^2+a*b+b^2+3)*traceSlope j x y

/-- Exact divided difference of the actual squared-trace block. -/
private def blockSlope {R : Type*} [CommRing R] (j : ℕ) (x y : R) : R :=
  (trace j x+trace j y)*traceSlope j x y

private theorem trace_diff {R : Type*} [CommRing R] (j : ℕ) (x y : R) :
    trace j x-trace j y=(x-y)*traceSlope j x y := by
  induction j with
  | zero => simp [trace,traceSlope]
  | succ j ih =>
    change step (trace j x)-step (trace j y)=
      (x-y)*((trace j x^2+trace j x*trace j y+trace j y^2+3)*traceSlope j x y)
    have h (a b : R) : step a-step b=(a-b)*(a^2+a*b+b^2+3) := by unfold step; ring
    rw [h,ih]
    ring

private theorem block_diff {R : Type*} [CommRing R] (j : ℕ) (x y : R) :
    block j x-block j y=(x-y)*blockSlope j x y := by
  have h := trace_diff j x y
  unfold block blockSlope
  linear_combination (trace j x+trace j y)*h

private theorem trace_add {R : Type*} [CommRing R] (i d : ℕ) (x : R) :
    trace (i+d) x=trace d (trace i x) := by
  induction d with
  | zero => simp [trace]
  | succ d ih =>
    change step (trace (i+d) x)=step (trace d (trace i x))
    rw [ih]

private theorem neg4_fixed {R : Type*} [CommRing R] {x : R} (h : x^2= -4) (d : ℕ) :
    (trace d x)^2= -4 := by
  induction d with
  | zero => simpa [trace] using h
  | succ d ih =>
    have he : step (trace d x)= -trace d x := by
      unfold step
      linear_combination (trace d x)*ih
    simp only [trace,he,neg_sq,ih]

private theorem earlier_factor {R : Type*} [CommRing R] (j i : ℕ) (hij : i < j) (x : R)
    (h : (trace i x)^2+1=0) : block j x= -1 := by
  have he : (trace (i+1) x)^2= -4 := by
    have hf : trace (i+1) x=2*trace i x := by
      simp only [trace,step]
      linear_combination (trace i x)*h
    rw [hf]
    linear_combination 4*h
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hij
  change j=i+1+d at hd
  unfold block
  rw [hd,trace_add,neg4_fixed he]
  ring

private theorem traceSlope_nonzero {K : Type*} [Field K] (h3 : (3:K)≠0)
    (j : ℕ) (x : K) (h : ∀ i<j, (trace i x)^2+1≠0) :
    traceSlope j x x≠0 := by
  induction j with
  | zero => simp [traceSlope]
  | succ j ih =>
    have hi := h j (Nat.lt_succ_self _)
    have he : (trace j x)^2+trace j x*trace j x+(trace j x)^2+3 =
        3*((trace j x)^2+1) := by ring
    change ((trace j x)^2+trace j x*trace j x+(trace j x)^2+3)*
      traceSlope j x x ≠ 0
    rw [he]
    exact mul_ne_zero (mul_ne_zero h3 hi) (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))

/-- Every root in characteristic other than two and three has a nonzero
diagonal divided difference. This is a denominator-free simple-root test. -/
private theorem root_slope_nonzero {K : Type*} [Field K] (h2 : (2:K)≠0) (h3 : (3:K)≠0)
    (j : ℕ) (x : K) (hx : block j x=0) : blockSlope j x x≠0 := by
  have hf (i : ℕ) (hi : i<j) : (trace i x)^2+1≠0 := by
    intro he
    have hc := earlier_factor j i hi x he
    rw [hx] at hc
    exact (neg_ne_zero.mpr (one_ne_zero : (1:K)≠0)) hc.symm
  have ht : trace j x≠0 := by
    intro he
    unfold block at hx
    simp [he] at hx
    exact h3 hx
  have hAdd : trace j x+trace j x≠0 := by rw [←two_mul]; exact mul_ne_zero h2 ht
  exact mul_ne_zero hAdd (traceSlope_nonzero h3 j x hf)



@[simp] private theorem map_trace {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (j : ℕ) (x : R) : ρ (trace j x)=trace j (ρ x) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [trace,step,map_add,map_mul,map_pow,map_ofNat,ih]

@[simp] private theorem map_block {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (j : ℕ) (x : R) : ρ (block j x)=block j (ρ x) := by
  simp only [block,map_add,map_pow,map_ofNat,map_trace]

@[simp] private theorem map_traceSlope {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (j : ℕ) (x y : R) : ρ (traceSlope j x y)=traceSlope j (ρ x) (ρ y) := by
  induction j with
  | zero => simp [traceSlope]
  | succ j ih => simp only [traceSlope,map_add,map_mul,map_pow,map_ofNat,map_trace,ih]

@[simp] private theorem map_blockSlope {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (j : ℕ) (x y : R) : ρ (blockSlope j x y)=blockSlope j (ρ x) (ρ y) := by
  simp only [blockSlope,map_mul,map_add,map_trace,map_traceSlope]

/-- At any positive precision two seeds in one mod-p root class are
carried by the actual block map with an invertible divided difference. -/
private theorem block_same_prime_disk {p a : ℕ} [Fact p.Prime] (ha : 0<a)
    (h2 : (2:ZMod p)≠0) (h3 : (3:ZMod p)≠0) (j : ℕ)
    (x y : ZMod (p^a)) :
    let ρ : ZMod (p^a) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
    ρ x=ρ y → block j (ρ x)=0 →
      ∃ U : (ZMod (p^a))ˣ, block j x-block j y=(x-y)*(U:ZMod (p^a)) := by
  dsimp only
  let ρ : ZMod (p^a) →+* ZMod p := ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
  change ρ x=ρ y → block j (ρ x)=0 → _
  intro hxy hx
  have hu : ρ (blockSlope j x y)≠0 := by
    rw [map_blockSlope,←hxy]
    exact root_slope_nonzero h2 h3 j (ρ x) hx
  have hp : Nat.Prime p := Fact.out
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set z := blockSlope j x y
  have hval : (z.val : ZMod (p^a))=z := ZMod.natCast_zmod_val z
  have hnd : ¬p ∣ z.val := by
    intro hh
    have he : (z.val : ZMod p)=0 := (ZMod.natCast_eq_zero_iff z.val p).mpr hh
    exact hu (by rw [←hval,map_natCast,he])
  have hc : z.val.Coprime (p^a) := (hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right _
  have hzu : IsUnit z := hval ▸ (ZMod.isUnit_iff_coprime z.val (p^a)).mpr hc
  obtain ⟨u,huv⟩ := hzu
  exact ⟨u,huv.symm ▸ block_diff j x y⟩



private theorem trace_odd_torsion_injective {K : Type*} [Field K] (h2 : (2:K)≠0)
    {N : ℕ} (hN : Odd N) (u v : Kˣ) (hu : u^N=1) (hv : v^N=1)
    (h : (u:K)-((u⁻¹:Kˣ):K) = (v:K)-((v⁻¹:Kˣ):K)) : u=v := by
  have huw : (u:K)*((u⁻¹:Kˣ):K)=1 := Units.mul_inv u
  have hvw : (v:K)*((v⁻¹:Kˣ):K)=1 := Units.mul_inv v
  have hf : ((u:K)-(v:K))*((u:K)*(v:K)+1)=0 := by
    linear_combination ((u:K)*(v:K))*h+(v:K)*huw-(u:K)*hvw
  rcases mul_eq_zero.mp hf with he|he
  · exact Units.ext (sub_eq_zero.mp he)
  · have hm : (u:K)*(v:K) = -1 := eq_neg_of_add_eq_zero_left he
    have hh : ((u:K)*(v:K))^N=1 := by
      rw [←Units.val_mul,←Units.val_pow_eq_pow_val,mul_pow,hu,hv]
      simp
    rw [hm,hN.neg_one_pow] at hh
    exact (h2 (by linear_combination -hh)).elim

/-- Exact Frobenius return criterion for a primitive cyclotomic parameter.
In characteristic not two, the signed trace has the identical cycle
length to its odd-order parameter. -/
private theorem trace_frobenius_iff {K : Type*} [Field K] {p : ℕ} [ExpChar K p]
    (h2 : (2:K)≠0) (u : Kˣ) (j a : ℕ) (hu : orderOf u=3^(j+1)) :
    let x : K := (u:K)-((u⁻¹:Kˣ):K)
    iterateFrobenius K p a x=x ↔ 3^(j+1) ∣ p^a-1 := by
  dsimp only
  let v := u^(p^a)
  have hN : Odd ((3:ℕ)^(j+1)) := (by decide : Odd (3:ℕ)).pow
  have he : u^3^(j+1)=1 := hu ▸ pow_orderOf_eq_one u
  have hv : v^3^(j+1)=1 := by
    dsimp [v]
    rw [pow_right_comm,he,one_pow]
  have hmap : iterateFrobenius K p a ((u:K)-((u⁻¹:Kˣ):K)) =
      (v:K)-((v⁻¹:Kˣ):K) := by
    rw [map_sub]
    change (u:K)^p^a-((u⁻¹:Kˣ):K)^p^a = (v:K)-((v⁻¹:Kˣ):K)
    rw [←Units.val_pow_eq_pow_val, ←Units.val_pow_eq_pow_val, inv_pow]
  rw [hmap]
  have hp : 0<p^a := pow_pos (expChar_pos K p) _
  constructor
  · intro h
    have hvu := trace_odd_torsion_injective h2 hN v u hv he h
    have heq : u^(p^a-1)=1 := by
      have hf : u^(p^a-1)*u=u := by
        rw [←pow_succ,show p^a-1+1=p^a by omega]
        exact hvu
      exact mul_right_cancel (hf.trans (one_mul u).symm)
    simpa only [←hu] using orderOf_dvd_of_pow_eq_one heq
  · intro h
    have heq : u^(p^a-1)=1 := orderOf_dvd_iff_pow_eq_one.mp (hu.symm ▸ h)
    have hvu : v=u := by
      dsimp [v]
      calc
        u^p^a = u^(p^a-1+1) := by rw [show p^a-1+1=p^a by omega]
        _ = u := by rw [pow_succ,heq,one_mul]
    rw [hvu]



/-- The variable-seed block is a bijection from each root's p-adic
residue disk to the zero disk, at every positive prime-power precision.
In particular, each mod-p root has exactly one compatible root lift. -/
private theorem block_disk_existsUnique {p a : ℕ} [Fact p.Prime] (ha : 0<a)
    (h2 : (2:ZMod p)≠0) (h3 : (3:ZMod p)≠0) (j : ℕ) (r : ZMod p)
    (hr : block j r=0) (s : ZMod (p^a)) :
    let ρ : ZMod (p^a) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
    ρ s=0 → ∃! x : ZMod (p^a), ρ x=r ∧ block j x=s := by
  dsimp only
  let ρ : ZMod (p^a) →+* ZMod p := ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
  change ρ s=0 → _
  intro hs
  have hp : Nat.Prime p := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let t : ZMod (p^a) := r.val
  have ht : ρ t=r := by
    dsimp [t]
    rw [map_natCast,ZMod.natCast_zmod_val]
  let U := { u : ZMod (p^a) // ρ u=0 }
  let f : U → U := fun z =>
    ⟨block j (t+(z:ZMod (p^a))), by
      rw [map_block,map_add,ht,z.property,add_zero,hr]⟩
  have hinj (x y : ZMod (p^a)) (hx : ρ x=r) (hy : ρ y=r)
      (he : block j x=block j y) : x=y := by
    obtain ⟨u,hu⟩ := block_same_prime_disk ha h2 h3 j x y (hx.trans hy.symm) (hx.symm ▸ hr)
    have hh : (x-y)*(u:ZMod (p^a))=0 := by rw [←hu,he,sub_self]
    have hz := congrArg (fun e => e*((u⁻¹:(ZMod (p^a))ˣ):ZMod (p^a))) hh
    rw [mul_assoc,Units.mul_inv,mul_one,zero_mul] at hz
    exact sub_eq_zero.mp hz
  have hfinj : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have hxy : t+(x:ZMod (p^a))=t+(y:ZMod (p^a)) := by
      apply hinj
      · rw [map_add,ht,x.property,add_zero]
      · rw [map_add,ht,y.property,add_zero]
      · exact congrArg Subtype.val he
    exact add_left_cancel hxy
  obtain ⟨z,hz⟩ := Finite.surjective_of_injective hfinj ⟨s,hs⟩
  refine ⟨t+(z:ZMod (p^a)), ⟨?_,congrArg Subtype.val hz⟩, ?_⟩
  · rw [map_add,ht,z.property,add_zero]
  · rintro y ⟨hy,he⟩
    apply hinj y _ hy
    · rw [map_add,ht,z.property,add_zero]
    · exact he.trans (congrArg Subtype.val hz).symm




/-- Companion factor for the quadratic norm of the free trace. -/
private def companion {R : Type*} [CommRing R] : ℕ → R → R
  | 0,_ => 1
  | j+1,x => ((trace j x)^2+1)*companion j x

private theorem companion_norm {R : Type*} [CommRing R] (j : ℕ) (x : R) :
    (x^2+4)*(companion j x)^2=(trace j x)^2+4 := by
  induction j with
  | zero => simp [companion,trace]
  | succ j ih =>
    simp only [companion,trace,step,mul_pow]
    rw [mul_left_comm,ih]
    ring

private theorem companion_unit {R : Type*} [CommRing R] (u : Rˣ) (j : ℕ) :
    (((u^3^j:Rˣ):R)+(((u⁻¹)^3^j:Rˣ):R)) =
      ((u:R)+((u⁻¹:Rˣ):R))*companion j ((u:R)-((u⁻¹:Rˣ):R)) := by
  induction j with
  | zero => simp [companion]
  | succ j ih =>
    simp only [companion,trace_unit]
    rw [←mul_left_comm,←ih]
    simp only [Units.val_pow_eq_pow_val,pow_succ (3:ℕ),pow_mul]
    let z : R := (u:R)^3^j
    let w : R := ((u⁻¹:Rˣ):R)^3^j
    change z^3+w^3=((z-w)^2+1)*(z+w)
    have h : z*w=1 := by
      dsimp [z,w]
      rw [←mul_pow]
      simp
    linear_combination (z+w)*h

/-- Every root has a primitive odd-order parameter already in its own
field. The explicit inverse companion factor supplies the square root
of the quadratic discriminant, so no extension or square-root axiom is
required. -/
private theorem root_has_primitive_parameter {K : Type*} [Field K] (h2 : (2:K)≠0)
    (h3 : (3:K)≠0) (j : ℕ) (x : K) (hx : block j x=0) :
    ∃ u : Kˣ, x=(u:K)-((u⁻¹:Kˣ):K) ∧ orderOf u=3^(j+1) := by
  let c := companion j x
  have hn : (x^2+4)*c^2=1 := by
    have hh := companion_norm j x
    change (x^2+4)*c^2=(trace j x)^2+4 at hh
    unfold block at hx
    linear_combination hh+hx
  have hc : c≠0 := by
    intro he
    rw [he,zero_pow (by decide : (2:ℕ)≠0),mul_zero] at hn
    exact zero_ne_one hn
  have hcInv : (c⁻¹)^2=x^2+4 := by
    rw [inv_pow, inv_eq_of_mul_eq_one_right (by simpa [mul_comm] using hn)]
  let z := (x-c⁻¹)/2
  let w := (-x-c⁻¹)/2
  have hzw : z*w=1 := by
    dsimp [z,w]
    rw [div_mul_div_comm]
    apply (div_eq_iff (mul_ne_zero h2 h2)).mpr
    linear_combination hcInv
  let u : Kˣ := ⟨z,w,hzw,by rwa [mul_comm]⟩
  have hTr : (u:K)-((u⁻¹:Kˣ):K)=x := by
    change z-w=x
    dsimp [z,w]
    rw [←sub_div]
    apply (div_eq_iff h2).mpr
    ring
  refine ⟨u,hTr.symm,?_⟩
  let v : Kˣ := u^3^j
  have he := companion_unit u j
  rw [hTr] at he
  change (v:K)+((v⁻¹:Kˣ):K)=(z+w)*c at he
  have hs : z+w= -c⁻¹ := by
    dsimp [z,w]
    rw [←add_div]
    apply (div_eq_iff h2).mpr
    ring
  rw [hs,neg_mul,inv_mul_cancel₀ hc] at he
  have hprod : (v:K)*((v⁻¹:Kˣ):K)=1 := Units.mul_inv v
  have hv2 : (v:K)^2+(v:K)+1=0 := by
    linear_combination (v:K)*he-hprod
  have hnv : v≠1 := by
    intro hh
    rw [hh] at hv2
    norm_num at hv2
    exact h3 hv2
  have hvc : (v:K)^3=1 := by
    linear_combination ((v:K)-1)*hv2
  have huc : u^3^(j+1)=1 := by
    rw [pow_succ (3:ℕ),pow_mul]
    exact Units.ext hvc
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime_pow hnv huc

/-- On every actual root, exact Frobenius period is the cyclotomic one. -/
private theorem root_frobenius_return {K : Type*} [Field K] {p : ℕ} [ExpChar K p]
    (h2 : (2:K)≠0) (h3 : (3:K)≠0) (j a : ℕ) (x : K)
    (hx : block j x=0) :
    iterateFrobenius K p a x=x ↔ 3^(j+1) ∣ p^a-1 := by
  obtain ⟨u,hu,hO⟩ := root_has_primitive_parameter h2 h3 j x hx
  rw [hu]
  exact trace_frobenius_iff h2 u j a hO



/-- Direct same-prime integer divisibility equivalence at every precision.
This is about the starting integer itself, not an auxiliary splitting
prime or a future block value. -/
private theorem block_integer_depth_difference {p a : ℕ} [Fact p.Prime] (ha : 0<a)
    (h2 : (2:ZMod p)≠0) (h3 : (3:ZMod p)≠0) (j : ℕ) (x y : ℤ)
    (hxy : (x:ZMod p)=(y:ZMod p)) (hx : block j (x:ZMod p)=0) :
    (↑(p^a):ℤ) ∣ block j x-block j y ↔ (↑(p^a):ℤ) ∣ x-y := by
  let ρ : ZMod (p^a) →+* ZMod p := ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
  have hL : ρ (x:ZMod (p^a))=ρ (y:ZMod (p^a)) := by simpa only [map_intCast] using hxy
  have hR : block j (ρ (x:ZMod (p^a)))=0 := by simpa only [map_intCast] using hx
  obtain ⟨u,hu⟩ := block_same_prime_disk ha h2 h3 j (x:ZMod (p^a)) (y:ZMod (p^a)) hL hR
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub]
  have hb (e : ℤ) : ((block j e : ℤ):ZMod (p^a)) = block j (e:ZMod (p^a)) :=
    map_block (Int.castRingHom (ZMod (p^a))) j e
  rw [hb,hb,hu]
  exact Units.mul_left_eq_zero u





/-- Bind the variable procedure at seed one to the protected golden Lucas
sequence rather than just comparing finite numerical levels. -/
private theorem seed_one_golden_trace (j : ℕ) : trace j (1:ℤ)=goldenLucas (3^j) := by
  induction j with
  | zero =>
    norm_num [trace,goldenLucas,D5.S0.Carrier.trace,D5.S0.Carrier.phi]
  | succ j ih =>
    by_cases hj : j=0
    · subst j
      norm_num [trace,step,goldenLucas,D5.S0.Carrier.trace,D5.S0.Carrier.phi,pow_succ]
    · have h := (golden_cubic_lucas_block j (by omega)).2.2.2.2.2
      change step (trace j (1:ℤ))=goldenLucas (3^(j+1))
      rw [ih,h]
      unfold step
      ring

private theorem seed_one_golden_block (j : ℕ) :
    block j (1:ℤ)=goldenLucas (3^j)^2+3 := by
  rw [block,seed_one_golden_trace]

/-- One integral polynomial per level, evaluated by the same readout in
characteristic zero, residue fields and prime-power rings. -/
noncomputable def variableBlock (j : ℕ) : Polynomial ℤ :=
  block j Polynomial.X

/-- Evaluate the integral readout in any commutative ring. -/
def read {R : Type} [CommRing R] (observed : ℕ → Polynomial ℤ) (j : ℕ) (x : R) : R :=
  (observed j).eval₂ (Int.castRingHom R) x

private theorem read_actual {R : Type} [CommRing R] (j : ℕ) (x : R) :
    read variableBlock j x = block j x := by
  change (Polynomial.eval₂RingHom (Int.castRingHom R) x) (block j Polynomial.X) = _
  rw [map_block]
  simp [Polynomial.eval₂RingHom]

/-- Cyclotomic signed-trace transport and exact same-prime disk law for
the same genuine polynomial readout. -/
def VariableTraceLaw (observed : ℕ → Polynomial ℤ) : Prop :=
  (∀ j : ℕ, read observed j (1:ℤ) = goldenLucas (3^j)^2+3) ∧
  (∀ (K : Type) [Field K] (_ : (2:K)≠0) (_ : (3:K)≠0) (j : ℕ) (x : K),
    read observed j x=0 ↔
      ∃! u : Kˣ, orderOf u=3^(j+1) ∧ x=(u:K)-((u⁻¹:Kˣ):K)) ∧
  (∀ (K : Type) [Field K] (p : ℕ) [ExpChar K p] (_ : (2:K)≠0) (_ : (3:K)≠0)
      (j a : ℕ) (x : K), read observed j x=0 →
    (iterateFrobenius K p a x=x ↔ 3^(j+1) ∣ p^a-1)) ∧
  (∀ (p a : ℕ) [Fact p.Prime] (ha : 0<a) (_ : (2:ZMod p)≠0) (_ : (3:ZMod p)≠0)
      (j : ℕ) (r : ZMod p) (s : ZMod (p^a)),
    let ρ : ZMod (p^a) →+* ZMod p := ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
    read observed j r=0 → ρ s=0 →
      ∃! x : ZMod (p^a), ρ x=r ∧ read observed j x=s) ∧
  (∀ (p a : ℕ) [Fact p.Prime] (_ : 0<a) (_ : (2:ZMod p)≠0) (_ : (3:ZMod p)≠0)
      (j : ℕ) (x y : ℤ), (x:ZMod p)=(y:ZMod p) → read observed j (x:ZMod p)=0 →
      ((↑(p^a):ℤ) ∣ read observed j x-read observed j y ↔ (↑(p^a):ℤ) ∣ x-y))

/-- Primitive signed traces are detected in their original field, and
each actual root disk bijects onto all same-prime zero-disk values at
every positive precision, preserving the exact prime-power depth of
differences between starting seeds in that disk. -/
theorem actual_variable_trace_root_disks :
    let observed := variableBlock
    VariableTraceLaw observed := by
  change VariableTraceLaw variableBlock
  unfold VariableTraceLaw
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    rw [read_actual,seed_one_golden_block]
  · intro K _ h2 h3 j x
    rw [read_actual]
    constructor
    · intro hx
      obtain ⟨u,hu,ho⟩ := root_has_primitive_parameter h2 h3 j x hx
      refine ⟨u,⟨ho,hu⟩,?_⟩
      rintro v ⟨hv,hv'⟩
      have ho' : Odd ((3:ℕ)^(j+1)) := (by decide : Odd (3:ℕ)).pow
      exact trace_odd_torsion_injective h2 ho' v u
        (hv ▸ pow_orderOf_eq_one v) (ho ▸ pow_orderOf_eq_one u) (hv'.symm.trans hu)
    · rintro ⟨u,⟨ho,hu⟩,_⟩
      have ho' : Odd ((3:ℕ)^(j+1)) := (by decide : Odd (3:ℕ)).pow
      rw [hu]
      exact (block_zero_iff_primitive h3 u j).2
        (((ho.symm ▸ ho').coprime_two_right.orderOf_pow).trans ho)
  · intro K _ p _ h2 h3 j a x hx
    rw [read_actual] at hx
    exact root_frobenius_return h2 h3 j a x hx
  · intro p a _ ha h2 h3 j r s
    dsimp only
    simp only [read_actual]
    intro hr hs
    exact block_disk_existsUnique ha h2 h3 j r hr s hs
  · intro p a _ ha h2 h3 j x y hxy hx
    rw [read_actual] at hx
    rw [read_actual,read_actual]
    exact block_integer_depth_difference ha h2 h3 j x y hxy hx

#print axioms actual_variable_trace_root_disks

end D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks
