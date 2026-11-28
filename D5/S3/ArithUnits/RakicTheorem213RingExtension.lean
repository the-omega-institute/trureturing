/- GID: D5/S3/ArithUnits/RakicTheorem213RingExtension
   generality: G
   mirror-B: D5/B/S3/ArithUnits/RakicTheorem213RingExtension
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Tactic.NoncommRing]
   utility: none
   digest: Four cubic identities characterize minus order with an additive group inverse. -/

module

public import D5.S3.ArithUnits.GolovanovBareDrazinEqualities
import Mathlib.Tactic.NoncommRing
import OmegaBuild.Commands
import all D5.S3.ArithUnits.GolovanovBareDrazinEqualities

/-! Rakić's difference criterion for group inverses in unital associative rings. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

namespace D5.S3.ArithUnits.RakicTheorem213RingExtension

open GolovanovBareDrazinEqualities (FD)

variable {R : Type*} [Ring R]

/-- A group inverse is a finite Drazin inverse with zero remainder. -/
@[expose] def GroupInv (x y : R) : Prop :=
  x * y * x = x ∧ FD x y

/-- The two-sided inner-inverse witness relation for the minus order. -/
@[expose] def MinusOrder (a b : R) : Prop :=
  ∃ u : R, a * u * a = a ∧ u * a = u * b ∧ a * u = b * u

private theorem equations {x y : R} :
    GroupInv x y ↔ x * y * x = x ∧ y * x * y = y ∧ x * y = y * x := by
  unfold GroupInv FD
  constructor
  · rintro ⟨hxyx, hyxy, hxy, _⟩
    exact ⟨hxyx, hyxy, hxy⟩
  · rintro ⟨hxyx, hyxy, hxy⟩
    exact ⟨hxyx, hyxy, hxy, ⟨1, by rw [pow_one, hxyx, sub_self]⟩⟩

private theorem support {x y : R} (h : GroupInv x y) :
    (x * y) * x = x ∧ x * (x * y) = x ∧ (x * y) * y = y ∧ y * (x * y) = y := by
  obtain ⟨hxyx, hyxy, hxy⟩ := equations.mp h
  exact ⟨hxyx, by rw [hxy, ← mul_assoc, hxyx], by rw [hxy, hyxy],
    by rw [← mul_assoc, hyxy]⟩

private theorem support_inverse {a α p : R} (ha : GroupInv a α)
    (hpa : p * a = a) (hap : a * p = a) :
    p * α = α ∧ α * p = α ∧ p * (a * α) = a * α ∧ (a * α) * p = a * α := by
  obtain ⟨_, _, h₁, h₂⟩ := support ha
  have hleft : p * α = α := by rw [← h₁, ← mul_assoc, ← mul_assoc, hpa, mul_assoc]
  have hright : α * p = α := by
    calc
      α * p = (α * (a * α)) * p := by rw [h₂]
      _ = α * (α * (a * p)) := by
        rw [(equations.mp ha).2.2]
        noncomm_ring
      _ = α := by rw [hap, ← (equations.mp ha).2.2, h₂]
  exact ⟨hleft, hright, by rw [← mul_assoc, hpa], by rw [mul_assoc, hright]⟩

private theorem minus_iff {a b β : R} (hb : GroupInv b β) :
    MinusOrder a b ↔ (b * β) * a = a ∧ a * (b * β) = a ∧ a * β * a = a := by
  obtain ⟨hpb, hbp, _, _⟩ := support hb
  have hbβ := (equations.mp hb).2.2
  constructor
  · rintro ⟨u, haua, hua, hau⟩
    have haub : a * u * b = a := by rw [mul_assoc, ← hua, ← mul_assoc, haua]
    have hbua : b * u * a = a := by rw [← hau, haua]
    refine ⟨?_, ?_, ?_⟩
    · calc
        (b * β) * a = (b * β) * (b * u * a) := by rw [hbua]
        _ = ((b * β) * b) * u * a := by noncomm_ring
        _ = a := by rw [hpb, hbua]
    · calc
        a * (b * β) = (a * u * b) * (b * β) := by rw [haub]
        _ = a * u * (b * (b * β)) := by noncomm_ring
        _ = a := by rw [hbp, haub]
    · calc
        a * β * a = (a * u * b) * β * (b * u * a) := by rw [haub, hbua]
        _ = a * u * (b * β * b) * u * a := by noncomm_ring
        _ = a := by rw [hpb, haub, haua]
  · rintro ⟨hpa, hap, hinner⟩
    let u := β * a * β
    have hau : a * u = a * β := by
      calc
        a * u = (a * β * a) * β := by dsimp [u]; noncomm_ring
        _ = a * β := by rw [hinner]
    have hua : u * a = β * a := by
      calc
        u * a = β * (a * β * a) := by dsimp [u]; noncomm_ring
        _ = β * a := by rw [hinner]
    have hbu : b * u = a * β := by
      calc
        b * u = ((b * β) * a) * β := by dsimp [u]; noncomm_ring
        _ = a * β := by rw [hpa]
    have hub : u * b = β * a := by
      calc
        u * b = β * (a * (β * b)) := by dsimp [u]; noncomm_ring
        _ = β * a := by rw [← hbβ, hap]
    exact ⟨u, by rw [hau, hinner], hua.trans hub.symm, hau.trans hbu.symm⟩

private theorem complement_inner {a b β : R} (hb : GroupInv b β)
    (hpa : (b * β) * a = a) (hap : a * (b * β) = a) (hinner : a * β * a = a) :
    (b - a) * β * (b - a) = b - a := by
  have hbβ := (equations.mp hb).2.2
  have hpb := (equations.mp hb).1
  calc
    (b - a) * β * (b - a) =
        b * β * b - (b * β) * a - a * (β * b) + a * β * a := by noncomm_ring
    _ = b - a := by rw [hpb, hpa, ← hbβ, hap, hinner]; abel

private theorem complement_products {a α b β : R} (ha : GroupInv a α) (hb : GroupInv b β)
    (hpa : (b * β) * a = a) (hap : a * (b * β) = a)
    (hz : (b - a) * α * (b - a) = 0) :
    let e := a * α
    let c := b - a
    let d := β - α
    d * c * d - d = α * b * α - α ∧
      c * d = b * β - b * e * β ∧ d * c = b * β - β * e * b := by
  dsimp
  obtain ⟨haInner, haOuter, haComm⟩ := equations.mp ha
  obtain ⟨_, hbOuter, hbComm⟩ := equations.mp hb
  obtain ⟨hpα, hαp, hpe, hep⟩ := support_inverse ha hpa hap
  let e := a * α
  have hZ : b * α * b - b * e - e * b + a = 0 := by
    calc
      _ = b * α * b - b * (α * a) - a * α * b + a * α * a := by
        rw [← haComm, haInner]
      _ = (b - a) * α * (b - a) := by noncomm_ring
      _ = 0 := hz
  have hright : b * α - b * e * β - e + a * β = 0 := by
    calc
      _ = b * (α * (b * β)) - b * e * β - e * (b * β) + a * β := by rw [hαp, hep]
      _ = (b * α * b - b * e - e * b + a) * β := by noncomm_ring
      _ = 0 := by rw [hZ, zero_mul]
  have hleft : α * b - e - β * e * b + β * a = 0 := by
    calc
      _ = ((β * b) * α) * b - (β * b) * e - β * e * b + β * a := by
        rw [← hbComm, hpα, hpe]
      _ = β * (b * α * b - b * e - e * b + a) := by noncomm_ring
      _ = 0 := by rw [hZ, mul_zero]
  have hboth : α - e * β - β * e + β * a * β = 0 := by
    calc
      _ = (β * b) * α - (β * b) * e * β - β * e + β * a * β := by
        rw [← hbComm, hpα, hpe]
      _ = β * (b * α - b * e * β - e + a * β) := by noncomm_ring
      _ = 0 := by rw [hright, mul_zero]
  have hβbα : β * b * α = α := by rw [← hbComm, hpα]
  have hαbβ : α * b * β = α := by rw [mul_assoc, hαp]
  have hβaα : β * a * α = β * e := by dsimp [e]; rw [mul_assoc]
  have hαaβ : α * a * β = e * β := by dsimp [e]; rw [← haComm]
  refine ⟨?_, ?_, ?_⟩
  · calc
      (β - α) * (b - a) * (β - α) - (β - α) =
          β * b * β - β * b * α - β * a * β + β * a * α -
          α * b * β + α * b * α + α * a * β - α * a * α - (β - α) := by
        noncomm_ring
      _ = α * b * α - α - (α - e * β - β * e + β * a * β) := by
        rw [hbOuter, hβbα, hαbβ, hβaα, hαaβ, haOuter]
        abel
      _ = _ := by rw [hboth, sub_zero]
  · calc
      (b - a) * (β - α) = b * β - b * e * β - (b * α - b * e * β - e + a * β) := by
        dsimp [e]
        noncomm_ring
      _ = _ := by rw [hright, sub_zero]
  · calc
      (β - α) * (b - a) = β * b - α * b - β * a + α * a := by noncomm_ring
      _ = b * β - β * e * b - (α * b - e - β * e * b + β * a) := by
        rw [← hbComm, ← haComm]
        abel
      _ = _ := by rw [hleft, sub_zero]

private theorem forward_products {a α b β : R} (ha : GroupInv a α) (hb : GroupInv b β)
    (hm : MinusOrder a b) (hc : GroupInv (b - a) (β - α)) :
    a ^ 3 = a * b * a ∧ a ^ 3 = a * b ^ 2 ∧ a ^ 3 = b ^ 2 * a := by
  obtain ⟨haInner, haOuter, haComm⟩ := equations.mp ha
  obtain ⟨hpa, hap, hinner⟩ := (minus_iff hb).mp hm
  obtain ⟨hcInner, hcOuter, hcComm⟩ := equations.mp hc
  have hcomp := complement_inner hb hpa hap hinner
  have hz : (b - a) * α * (b - a) = 0 := by
    apply sub_eq_zero.mp
    calc
      (b - a) * α * (b - a) - 0 =
          (b - a) * β * (b - a) - (b - a) * (β - α) * (b - a) := by noncomm_ring
      _ = 0 := by rw [hcomp, hcInner, sub_self]
  obtain ⟨hd, hcd, hdc⟩ := complement_products ha hb hpa hap hz
  have hαbα : α * b * α = α := by rw [hcOuter, sub_self] at hd; exact sub_eq_zero.mp hd.symm
  let e := a * α
  have hebe : e * b * e = a := by
    calc
      e * b * e = a * (α * b * α) * a := by
        calc
          e * b * e = (a * α) * b * (α * a) := by rw [← haComm]
          _ = _ := by noncomm_ring
      _ = a := by rw [hαbα, haInner]
  have heβe : e * β * e = α := by
    calc
      e * β * e = α * (a * β * a) * α := by
        calc
          e * β * e = (α * a) * β * (a * α) := by rw [← haComm]
          _ = _ := by noncomm_ring
      _ = α := by rw [hinner, haOuter]
  have heab : e * a = a := haInner
  have hae : a * e = a := (support ha).2.1
  have hbe : b * e * β = β * e * b := by
    apply sub_right_inj.mp
    exact hcd.symm.trans (hcComm.trans hdc)
  obtain ⟨_, _, hpe, hep⟩ := support_inverse ha hpa hap
  have hb2e : b ^ 2 * e = e * b ^ 2 := by
    calc
      b ^ 2 * e = b * (b * e * β) * b := by
        calc
          b ^ 2 * e = b ^ 2 * (e * (β * b)) := by rw [← (equations.mp hb).2.2, hep]
          _ = _ := by noncomm_ring
      _ = b * (β * e * b) * b := by rw [hbe]
      _ = e * b ^ 2 := by
        calc
          b * (β * e * b) * b = ((b * β) * e) * b ^ 2 := by noncomm_ring
          _ = _ := by rw [hpe]
  have hb2β : b ^ 2 * β = b := by rw [pow_two, mul_assoc, (support hb).2.1]
  have hee : e * e = e := by
    calc
      e * e = (e * a) * α := (mul_assoc e a α).symm
      _ = e := by rw [heab]
  have hb2eα : b ^ 2 * e * α = a := by
    calc
      b ^ 2 * e * α = b ^ 2 * e * (e * β * e) := by rw [heβe]
      _ = b ^ 2 * (e * e) * β * e := by noncomm_ring
      _ = (b ^ 2 * e) * β * e := by rw [hee]
      _ = e * (b ^ 2 * β) * e := by rw [hb2e, mul_assoc e]
      _ = a := by rw [hb2β, hebe]
  have hb2e' : b ^ 2 * e = a ^ 2 := by
    calc
      b ^ 2 * e = b ^ 2 * e * α * a := by
        calc
          b ^ 2 * e = b ^ 2 * ((e * α) * a) := by
            rw [(support ha).2.2.1, ← haComm]
          _ = _ := by noncomm_ring
      _ = a ^ 2 := by rw [hb2eα, pow_two]
  refine ⟨?_, ?_, ?_⟩
  · calc
      a ^ 3 = a * (e * b * e) * a := by rw [hebe, pow_succ, pow_two]
      _ = (a * e) * b * (e * a) := by noncomm_ring
      _ = _ := by rw [hae, heab]
  · calc
      a ^ 3 = a * (e * b ^ 2) := by
        rw [← hb2e, hb2e']
        noncomm_ring
      _ = (a * e) * b ^ 2 := (mul_assoc a e _).symm
      _ = _ := by rw [hae]
  · calc
      a ^ 3 = (b ^ 2 * e) * a := by rw [hb2e', pow_succ]
      _ = b ^ 2 * (e * a) := by rw [mul_assoc]
      _ = _ := by rw [heab]

private theorem reverse {a α b β : R} (ha : GroupInv a α) (hb : GroupInv b β)
    (haba : a ^ 3 = a * b * a) (hab2 : a ^ 3 = a * b ^ 2) (hb2a : a ^ 3 = b ^ 2 * a)
    (hcube : (b - a) ^ 3 = b ^ 3 - a ^ 3) :
    MinusOrder a b ∧ GroupInv (b - a) (β - α) := by
  obtain ⟨haInner, haOuter, haComm⟩ := equations.mp ha
  obtain ⟨hbInner, _, hbComm⟩ := equations.mp hb
  obtain ⟨hea, hae, heα, hαe⟩ := support ha
  let e := a * α
  let p := b * β
  have ha2α : a ^ 2 * α = a := by rw [pow_two, mul_assoc, hae]
  have ha3α : a ^ 3 * α = a ^ 2 := by
    calc
      a ^ 3 * α = a * (a ^ 2 * α) := by noncomm_ring
      _ = _ := by rw [ha2α, pow_two]
  have ha3α2 : a ^ 3 * α ^ 2 = a := by rw [pow_two, ← mul_assoc, ha3α, ha2α]
  have hcomm : Commute a α := haComm
  have hα2a3 : α ^ 2 * a ^ 3 = a := ((hcomm.pow_left 3).pow_right 2).eq.symm.trans ha3α2
  have hpbb : p * b ^ 2 = b ^ 2 := by rw [pow_two, ← mul_assoc, hbInner]
  have hbbp : b ^ 2 * p = b ^ 2 := by rw [pow_two, mul_assoc, (support hb).2.1]
  have hpa : p * a = a := by
    calc
      p * a = p * ((b ^ 2 * a) * α ^ 2) := by rw [← hb2a, ha3α2]
      _ = (p * b ^ 2) * a * α ^ 2 := by noncomm_ring
      _ = _ := by rw [hpbb, ← hb2a, ha3α2]
  have hap : a * p = a := by
    calc
      a * p = (α ^ 2 * (a * b ^ 2)) * p := by rw [← hab2, hα2a3]
      _ = α ^ 2 * a * (b ^ 2 * p) := by noncomm_ring
      _ = α ^ 2 * (a * b ^ 2) := by rw [hbbp, mul_assoc]
      _ = _ := by rw [← hab2, hα2a3]
  obtain ⟨hpα, _, _, _⟩ := support_inverse ha hpa hap
  have hebe : e * b * e = a := by
    calc
      e * b * e = α * (a * b * a) * α := by
        calc
          e * b * e = (α * a) * b * (a * α) := by rw [← haComm]
          _ = _ := by noncomm_ring
      _ = α * a ^ 2 := by rw [← haba, mul_assoc, ha3α]
      _ = _ := by rw [pow_two, ← mul_assoc, ← haComm, haInner]
  have hαbα : α * b * α = α := by
    calc
      α * b * α = α * (e * b * e) * α := by
        calc
          α * b * α = (α * e) * b * (e * α) := by rw [hαe, heα]
          _ = _ := by noncomm_ring
      _ = _ := by rw [hebe, haOuter]
  have hb2e : b ^ 2 * e = a ^ 2 := by rw [← mul_assoc, ← hb2a, ha3α]
  have heb2 : e * b ^ 2 = a ^ 2 := by
    change a * α * b ^ 2 = _
    rw [haComm, mul_assoc, ← hab2]
    exact ((hcomm.pow_left 3).eq.symm.trans ha3α)
  have hb2α : b ^ 2 * α = a := by
    calc
      b ^ 2 * α = (b ^ 2 * e) * α := by rw [mul_assoc, heα]
      _ = _ := by rw [hb2e, ha2α]
  have hαb2 : α * b ^ 2 = a := by
    calc
      α * b ^ 2 = α * (e * b ^ 2) := by rw [← mul_assoc, hαe]
      _ = _ := by rw [heb2]; exact (hcomm.pow_left 2).eq.symm.trans ha2α
  have hbα : b * α = β * a := by
    calc
      b * α = p * (b * α) := by rw [← mul_assoc, hbInner]
      _ = β * (b ^ 2 * α) := by dsimp [p]; rw [hbComm]; noncomm_ring
      _ = _ := by rw [hb2α]
  have hαb : α * b = a * β := by
    calc
      α * b = (α * b) * p := by rw [mul_assoc, (support hb).2.1]
      _ = (α * b ^ 2) * β := by dsimp [p]; noncomm_ring
      _ = _ := by rw [hαb2]
  have hβ2a : β ^ 2 * a = α := by
    rw [pow_two, mul_assoc, ← hbα, ← mul_assoc, ← hbComm, hpα]
  have hinner : a * β * a = a := by
    calc
      a * β * a = α * b * a := by rw [← hαb]
      _ = α * (e * b * e) * a := by
        calc
          α * b * a = (α * e) * b * (e * a) := by rw [hαe, hea]
          _ = _ := by noncomm_ring
      _ = a := by rw [hebe, ← haComm, haInner]
  have hword : b * a * b = b * a ^ 2 + a ^ 2 * b - a ^ 3 := by
    apply sub_eq_zero.mp
    calc
      _ = (b ^ 3 - a ^ 3) - (b - a) ^ 3 -
          (b ^ 2 * a - a ^ 3) - (a * b ^ 2 - a ^ 3) + (a * b * a - a ^ 3) := by
        noncomm_ring
      _ = 0 := by simp only [hcube, ← hb2a, ← hab2, ← haba, sub_self, add_zero]
  have hβ2b : β ^ 2 * b = b * β ^ 2 := (show Commute β b from hbComm.symm).pow_left 2
  have hbαb : b * α * b = b * e + e * b - a := by
    calc
      b * α * b = β ^ 2 * (b * a * b) := by
        calc
          b * α * b = b * (β ^ 2 * a) * b := by rw [hβ2a]
          _ = (b * β ^ 2) * a * b := by noncomm_ring
          _ = β ^ 2 * (b * a * b) := by rw [← hβ2b]; noncomm_ring
      _ = β ^ 2 * (b * a ^ 2 + a ^ 2 * b - a ^ 3) := by rw [hword]
      _ = b * ((β ^ 2 * a) * a) + (β ^ 2 * a) * a * b - (β ^ 2 * a) * a * a := by
        calc
          _ = (β ^ 2 * b) * a * a + (β ^ 2 * a) * a * b - (β ^ 2 * a) * a * a := by
            noncomm_ring
          _ = _ := by rw [hβ2b]; noncomm_ring
      _ = _ := by rw [hβ2a, ← haComm, haInner]
  have hz : (b - a) * α * (b - a) = 0 := by
    calc
      _ = b * α * b - b * e - e * b + a := by
        calc
          _ = b * α * b - b * (α * a) - (a * α) * b + a * α * a := by noncomm_ring
          _ = _ := by rw [← haComm, haInner]
      _ = 0 := by rw [hbαb]; abel
  obtain ⟨hd, _, _⟩ := complement_products ha hb hpa hap hz
  refine ⟨(minus_iff hb).mpr ⟨hpa, hap, hinner⟩, equations.mpr ⟨?_, ?_, ?_⟩⟩
  · calc
      (b - a) * (β - α) * (b - a) =
          (b - a) * β * (b - a) - (b - a) * α * (b - a) := by noncomm_ring
      _ = _ := by rw [complement_inner hb hpa hap hinner, hz, sub_zero]
  · exact sub_eq_zero.mp (hd.trans (sub_eq_zero.mpr hαbα))
  · calc
      (b - a) * (β - α) = b * β - b * α - a * β + a * α := by noncomm_ring
      _ = β * b - β * a - α * b + α * a := by rw [hbComm, hbα, ← hαb, haComm]
      _ = (β - α) * (b - a) := by noncomm_ring

/-- Rakić's four cubic identities characterize the minus relation and group inverse
of the difference over every unital associative ring. -/
theorem result (a α b β : R) (ha : GroupInv a α) (hb : GroupInv b β) :
    (MinusOrder a b ∧ GroupInv (b - a) (β - α)) ↔
      (a ^ 3 = a * b * a ∧ a ^ 3 = a * b ^ 2 ∧ a ^ 3 = b ^ 2 * a ∧
        (b - a) ^ 3 = b ^ 3 - a ^ 3) := by
  constructor
  · rintro ⟨hm, hc⟩
    obtain ⟨haba, hab2, hb2a⟩ := forward_products ha hb hm hc
    obtain ⟨hpa, hap, hinner⟩ := (minus_iff hb).mp hm
    have hpc : (b * β) * (b - a) = b - a := by rw [mul_sub, (support hb).1, hpa]
    have hcp : (b - a) * (b * β) = b - a := by rw [sub_mul, (support hb).2.1, hap]
    have hmc := (minus_iff hb).mpr ⟨hpc, hcp, complement_inner hb hpa hap hinner⟩
    have hac : GroupInv (b - (b - a)) (β - (β - α)) := by
      simpa only [sub_sub_cancel] using ha
    refine ⟨haba, hab2, hb2a, (forward_products hc hb hmc hac).2.2.trans ?_⟩
    rw [mul_sub, ← hb2a, ← pow_succ b 2]
  · rintro ⟨haba, hab2, hb2a, hcube⟩
    exact reverse ha hb haba hab2 hb2a hcube

end D5.S3.ArithUnits.RakicTheorem213RingExtension
