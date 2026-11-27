/- GID: D5/S3/Arith/Primes/GoldenCubicInertFrobeniusReadout
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicInertFrobeniusReadout
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: One short norm-one power determines the actual rational Frobenius action on inert cubic branches. -/

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout

/-- Norm-one cubic readout using exponent (q+1)/3, not (q²−1)/3. -/
private theorem inert_shortcut {K : Type*} [Field K] (q : ℕ) (β B : K)
    (hq : q % 3 = 2) (hB : B ≠ 0) (hnorm : β^(q+1) = B^3)
    (hfix : B^(q-1) = 1) :
    let ε := β^((q+1)/3)/B
    ε^3=1 ∧ β^((q^2-1)/3)=ε := by
  let m := (q+1)/3
  let ε := β^m/B
  have hm : m*3 = q+1 := by dsimp [m]; omega
  have he : ε^3=1 := by
    dsimp [ε]
    rw [div_pow, ←pow_mul, hm, hnorm, div_self (pow_ne_zero _ hB)]
  have hq2 : (q^2-1)/3=m*(q-1) := by
    have hq' : 0<q := by omega
    have hq1 : q-1+1=q := by omega
    have heq : q^2-1=3*(m*(q-1)) := by
      have hf : q^2=(q+1)*(q-1)+1 := by
        calc
          q^2 = (q-1+1)^2 := by rw [hq1]
          _ = ((q-1+1)+1)*(q-1)+1 := by ring
          _ = _ := by rw [hq1]
      rw [hf, Nat.add_sub_cancel, ←hm]
      ring
    rw [heq]
    exact Nat.mul_div_cancel_left _ (by decide)
  have hbε : β^m=B*ε := by
    dsimp [ε]
    rw [mul_comm B, div_mul_cancel₀ _ hB]
  have hε : ε^(q-1)=ε := by
    have hr : q-1=3*(q/3)+1 := by omega
    rw [hr,pow_succ,pow_mul,he,one_pow,one_mul]
  refine ⟨he,?_⟩
  change β^((q^2-1)/3)=ε
  calc
    β^((q^2-1)/3) = (β^m)^(q-1) := by rw [hq2,pow_mul]
    _ = (B*ε)^(q-1) := congrArg (fun z => z^(q-1)) hbε
    _ = ε := by rw [mul_pow,hfix,hε,one_mul]

/-- Cardano branch labeled by a root of unity. -/
def cardanoTerm {K : Type*} [Field K] (B c a : K) : K :=
  a*c + a⁻¹*(B/c)

/-- Inert Frobenius swaps the two cube radicals, making the branch shift by the
inverse of the character witness. A ring map allows use of ordinary finite-field Frobenius. -/
private theorem cardano_inert_map {K : Type*} [Field K] (σ : K →+* K) (B c a ε : K)
    (hB : B≠0)
    (hσB:σ B=B) (hσa:σ a=a⁻¹) (hσc:σ c=ε*B/c) :
    σ (cardanoTerm B c a)=cardanoTerm B c (a/ε) := by
  simp only [cardanoTerm,map_add,map_mul,map_inv₀,map_div₀,hσB,hσa,hσc,inv_inv]
  simp [div_eq_mul_inv]
  calc
    _ = a * c * ε⁻¹ * (B * B⁻¹) + a⁻¹ * B * c⁻¹ * ε := by ring
    _ = _ := by rw [mul_inv_cancel₀ hB,mul_one]; ring

section
variable {K : Type*} [Field K]

private def t (c d a : K) : K := a*c + a⁻¹*d

private theorem roots {x δ B c d a : K} (hc : c^3=B*(-x+δ)) (hd : d^3=B*(-x-δ))
    (hcd : c*d=B) (ha : a^3=1) :
    (t c d a)^3 - 3*B*(t c d a) + 2*B*x = 0 := by
  have hai : (a⁻¹)^3=1 := by rw [inv_pow,ha,inv_one]
  have hane : a ≠ 0 := by intro h; simp [h] at ha
  have hap : (a*c)*(a⁻¹*d) = B := by
    calc
      _ = (a*a⁻¹)*(c*d) := by ring
      _ = B := by rw [mul_inv_cancel₀ hane,one_mul,hcd]
  have he : (a*c + a⁻¹*d)^3 - 3*((a*c)*(a⁻¹*d))*(a*c+a⁻¹*d) =
      (a*c)^3+(a⁻¹*d)^3 := by ring
  rw [hap,mul_pow,mul_pow,ha,hai,one_mul,one_mul,hc,hd] at he
  unfold t
  rw [he]
  ring

private theorem labels_inj {c d a b : K} (hcd : c^3 ≠ d^3) (ha : a^3=1) (hb : b^3=1)
    (h : t c d a = t c d b) : a=b := by
  by_contra hab
  have hane : a ≠ 0 := by intro h'; simp [h'] at ha
  have hbne : b ≠ 0 := by intro h'; simp [h'] at hb
  have hmul : a*b ≠ 0 := mul_ne_zero hane hbne
  have hh := congrArg (fun z : K => (a*b)*z) h
  dsimp [t] at hh
  have h1 : (a*b)*(a⁻¹*d) = b*d := by
    calc
      _ = (a*a⁻¹)*(b*d) := by ring
      _ = b*d := by rw [mul_inv_cancel₀ hane,one_mul]
  have h2 : (a*b)*(b⁻¹*d) = a*d := by
    calc
      _ = (b*b⁻¹)*(a*d) := by ring
      _ = a*d := by rw [mul_inv_cancel₀ hbne,one_mul]
  have he : (a-b)*((a*b)*c-d) = 0 := by
    calc
      _ = (a*b)*(a*c)+b*d-((a*b)*(b*c)+a*d) := by ring
      _ = 0 := sub_eq_zero.mpr (by simpa only [mul_add,h1,h2] using hh)
  have hz : (a*b)*c=d := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hab))
  apply hcd
  have h3 := congrArg (fun z : K => z^3) hz
  simpa [mul_pow,ha,hb] using h3

end

theorem native_inert_readout {K : Type*} [Field K] (q : ℕ) [CharP K q]
    (hp : q.Prime) (hqgt : 3<q) (hq : q%3=2) (x δ : K)
    (hδ : δ^2=-3) (hδF : δ^q = -δ) (hx : x^q=x)
    (hB : x^2+3 ≠ 0) :
    let B := x^2+3
    let β := B*(-x+δ)
    let ω := (δ-1)/2
    let ε := β^((q+1)/3)/B
    ε^3=1 ∧ β^((q^2-1)/3)=ε ∧ ω^3=1 ∧ ω≠1 ∧
      ∀ c : K, c^3=β →
      (∀ a : K, a^3=1 →
        (cardanoTerm B c a)^3 - 3*B*cardanoTerm B c a + 2*B*x=0 ∧
        (cardanoTerm B c a)^q=cardanoTerm B c (a/ε)) ∧
      (∀ a b : K, a^3=1 → b^3=1 → cardanoTerm B c a=cardanoTerm B c b → a=b) ∧
      ((cardanoTerm B c 1)^q=cardanoTerm B c 1 ↔ ε=1) := by
  let _ : ExpChar K q := .prime hp
  let B := x^2+3
  let β := B*(-x+δ)
  let ω := (δ-1)/2
  let ε := β^((q+1)/3)/B
  change ε^3=1 ∧ β^((q^2-1)/3)=ε ∧ ω^3=1 ∧ ω≠1 ∧ _
  let σ := frobenius K q
  have hxσ : σ x=x := hx
  have hδσ : σ δ=-δ := hδF
  have hBσ : σ B=B := by unfold B; simp only [map_add,map_pow,hxσ,map_ofNat]
  have hβσ : σ β=B*(-x-δ) := by
    unfold β
    rw [map_mul,hBσ,map_add,map_neg,hxσ,hδσ,sub_eq_add_neg]
  have hnorm : β^(q+1)=B^3 := by
    rw [pow_succ,show β^q=σ β from rfl,hβσ]
    calc
      B*(-x-δ)*β = B^2*(x^2-δ^2) := by unfold β; ring
      _ = B^3 := by rw [hδ]; unfold B; ring
  have hfix : B^(q-1)=1 := by
    apply mul_left_cancel₀ (show B≠0 from hB)
    rw [mul_comm B,←pow_succ,show q-1+1=q by omega,mul_one]
    exact hBσ
  have htwo : (2:K) ≠ 0 := by
    intro z
    exact (not_le_of_gt (show 2<q by omega))
      (Nat.le_of_dvd (by decide) ((CharP.cast_eq_zero_iff K q 2).mp z))
  have hthree : (3:K) ≠ 0 := by
    intro z
    exact (not_le_of_gt hqgt) (Nat.le_of_dvd (by decide) ((CharP.cast_eq_zero_iff K q 3).mp z))
  have hωquad : ω^2+ω+1=0 := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 htwo : (2:K)^2 ≠ 0))
    rw [mul_zero]
    calc
      (2:K)^2*(ω^2+ω+1) = δ^2+3 := by
        unfold ω
        simp only [div_eq_mul_inv, mul_pow]
        calc
          _ = ((2:K)*(2:K)⁻¹)^2*(δ-1)^2 + (2:K)*((2:K)*(2:K)⁻¹)*(δ-1)+4 := by ring
          _ = _ := by rw [mul_inv_cancel₀ htwo]; ring
      _ = _ := by rw [hδ]; ring
  have hωcube : ω^3=1 := by
    apply sub_eq_zero.mp
    calc
      _ = (ω-1)*(ω^2+ω+1) := by ring
      _ = 0 := by rw [hωquad,mul_zero]
  have hωne : ω ≠ 1 := by
    intro he
    rw [he] at hωquad
    apply hthree
    calc (3:K)=1^2+1+1 := by ring
         _=0 := hωquad
  obtain ⟨he,hepow⟩ := inert_shortcut q β B hq hB hnorm hfix
  refine ⟨he,hepow,hωcube,hωne,?_⟩
  intro c hc
  have hcne : c≠0 := by
    intro hz
    have he : β=0 := by simpa [hz,β] using hc.symm
    have hB0 := hnorm
    rw [he,zero_pow (by omega : q+1 ≠ 0)] at hB0
    exact pow_ne_zero _ hB hB0.symm
  have hcσ : σ c=ε*B/c := by
    apply (eq_div_iff hcne).2
    change c^q*c=ε*B
    calc
      c^q*c = c^(q+1) := (pow_succ c q).symm
      _ = (c^3)^((q+1)/3) := by rw [←pow_mul,show 3*((q+1)/3)=q+1 by omega]
      _ = ε*B := by rw [hc]; exact (div_mul_cancel₀ (β^((q+1)/3)) hB).symm
  have hωσ : ∀ a : K, a^3=1 → σ a=a⁻¹ := by
    intro a ha
    have hane : a≠0 := by intro hz; simp [hz] at ha
    change a^q=a⁻¹
    rw [show q=3*(q/3)+2 by omega,pow_add,pow_mul,ha,one_pow,one_mul]
    apply mul_right_cancel₀ hane
    rw [←pow_succ,ha,inv_mul_cancel₀ hane]
  have hcb : c^3=β := hc
  have hβne : β≠0 := hcb ▸ pow_ne_zero 3 hcne
  let d := B/c
  have hcd : c*d=B := by
    dsimp [d]
    rw [mul_comm,div_mul_cancel₀ _ hcne]
  have hd : d^3=B*(-x-δ) := by
    apply mul_right_cancel₀ hβne
    calc
      d^3*β = B^3 := by rw [←hcb,←mul_pow,mul_comm d c,hcd]
      _ = (B*(-x-δ))*β := by
        unfold β
        calc
          _ = B^2*(x^2-δ^2) := by rw [hδ]; unfold B; ring
          _ = _ := by ring
  have hδne : δ≠0 := by
    intro hz
    apply hthree
    simpa [hz] using hδ.symm
  have hcdiff : c^3≠d^3 := by
    intro hh
    have hzero : 2*B*δ=0 := by
      calc
        _ = β-B*(-x-δ) := by unfold β; ring
        _ = 0 := by rw [←hd,←hcb,hh,sub_self]
    exact (mul_ne_zero (mul_ne_zero htwo hB) hδne) hzero
  have hroots (a : K) (ha : a^3=1) :
      (cardanoTerm B c a)^3 - 3*B*cardanoTerm B c a + 2*B*x=0 :=
    roots hc hd hcd ha
  have htrans (a : K) (ha : a^3=1) :
      (cardanoTerm B c a)^q=cardanoTerm B c (a/ε) :=
    cardano_inert_map σ B c a ε hB hBσ (hωσ a ha) hcσ
  have hinj (a b : K) (ha : a^3=1) (hb : b^3=1)
      (h : cardanoTerm B c a=cardanoTerm B c b) : a=b := labels_inj hcdiff ha hb h
  refine ⟨fun a ha => ⟨hroots a ha,htrans a ha⟩,hinj,?_⟩
  have tr := htrans 1 (one_pow 3)
  change (cardanoTerm B c 1)^q=cardanoTerm B c 1 ↔ ε=1
  constructor
  · intro h
    have hε : (1/ε)^3=1 := by rw [div_pow,he,one_pow,div_one]
    have hin := hinj _ _ hε (one_pow 3) (tr.symm.trans h)
    simpa only [one_div,inv_eq_one] using hin
  · intro hz
    simpa only [hz,div_one] using tr

end D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
#print axioms D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout.native_inert_readout
