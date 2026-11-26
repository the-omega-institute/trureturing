/- GID: D5/S3/Arith/Primes/GoldenCubicDyadicRootLocus
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicDyadicRootLocus
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The native rational Cardano cubic has exact dyadic root classes at arbitrary depth. -/

import D5.S1.Scale.GoldenCubicBlockCongruences

namespace D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
open D5.S1.Scale

def halfCubic (B x s : ℤ) : ℤ := 4*s^3-3*B*s+B*x

private theorem halfCubic_even_root_to_depth (B x : ℤ)
    (hB : Odd B) (hx : Even x) (n : ℕ) :
    ∃ z : ℤ, Even z ∧ (2 : ℤ)^(n+1) ∣ halfCubic B x z := by
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a, ha⟩ := hx
  induction n with
  | zero =>
    refine ⟨0, by decide, B*a, ?_⟩
    unfold halfCubic
    rw [ha]
    ring
  | succ n ih =>
    obtain ⟨z, ⟨w, hw⟩, ⟨t, ht⟩⟩ := ih
    let v : ℤ := 2^n
    have hv : (2 : ℤ)^(n+1) = 2*v := by rw [pow_succ, mul_comm]
    have hv' : (2 : ℤ)^(n+1+1) = 4*v := by rw [pow_succ, hv]; ring
    rw [hv] at ht
    refine ⟨z-2*v*t, ⟨w-v*t, ?_⟩, ?_⟩
    · rw [hw]; ring
    rw [hv']
    refine ⟨t*(2+3*b-6*z^2+12*z*v*t-8*v^2*t^2), ?_⟩
    calc
      halfCubic B x (z-2*v*t) = halfCubic B x z+
          (halfCubic B x (z-2*v*t)-halfCubic B x z) := by ring
      _ = halfCubic B x z + (-2*v*t)*(12*z^2-3*B+12*z*(-2*v*t)+4*(-2*v*t)^2) := by
        unfold halfCubic
        ring
      _ = _ := by rw [ht,hb]; ring

private theorem odd_inverse_to_depth (d : ℤ) (hd : Odd d) (n : ℕ) :
    ∃ u : ℤ, Odd u ∧ (2 : ℤ)^(n+1) ∣ d*u-1 := by
  obtain ⟨e, he⟩ := hd
  induction n with
  | zero =>
    refine ⟨1, by decide, e, ?_⟩
    rw [he]; ring
  | succ n ih =>
    obtain ⟨u, ⟨w, hw⟩, ⟨t, ht⟩⟩ := ih
    let v : ℤ := 2^n
    have hv : (2 : ℤ)^(n+1) = 2*v := by rw [pow_succ, mul_comm]
    have hv' : (2 : ℤ)^(n+1+1) = 4*v := by rw [pow_succ, hv]; ring
    rw [hv] at ht
    refine ⟨u-2*v*t, ⟨w-v*t, ?_⟩, ?_⟩
    · rw [hw]; ring
    rw [hv']
    refine ⟨-e*t, ?_⟩
    calc
      _ = (d*u-1)-d*2*v*t := by ring
      _ = _ := by rw [ht,he]; ring

private theorem factor_square {R : Type*} [CommRing R] (x s u : R)
    (h : 4*s^3-3*(x^2+3)*s+(x^2+3)*x=0)
    (hu : (4*s^2-(x^2+3))*u=1) :
    (3*(x^2+3)*u)^2 = 3*(x^2+3)-3*s^2 := by
  let B : R := x^2+3
  let d : R := 4*s^2-B
  let g : R := 4*s^3-3*B*s
  have h' : g+B*x=0 := h
  have hu' : d*u=1 := hu
  have hsquare : d^2*(3*B-3*s^2)-9*B^2 = 0 := by
    calc
      _ = (3*(B*x-g))*(g+B*x) := by dsimp [B,d,g]; ring
      _ = 0 := by rw [h',mul_zero]
  have hv : d^2*(3*B-3*s^2)=9*B^2 := sub_eq_zero.mp hsquare
  change (3*B*u)^2 = 3*B-3*s^2
  calc
    _ = u^2*(9*B^2) := by ring
    _ = (d*u)^2*(3*B-3*s^2) := by rw [← hv]; ring
    _ = _ := by rw [hu',one_pow,one_mul]

private theorem cast_dvd (m : ℕ) (z : ℤ) (hz : (m : ℤ) ∣ z) :
    (z : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z m).2 hz

/-- The *rational* Cardano cubic splits over every dyadic residue ring. Its
three branches have one even root and two odd roots separated modulo four.
Unlike the Eisenstein squarefree lift, the polynomial has a double root mod 2. -/
private theorem real_cubic_dyadic_split (x : ℤ) (hx : Even x) (n : ℕ) :
    let B : ℤ := x^2+3
    let m := 2^(n+1)
    ∃ e p q : ℤ, Even e ∧ Odd p ∧ Odd q ∧ Odd ((p-q)/2) ∧
      ∀ t : ZMod m, t^3-3*(B : ZMod m)*t+2*(B : ZMod m)*(x : ZMod m) =
        (t-(e : ZMod m))*(t-(p : ZMod m))*(t-(q : ZMod m)) := by
  dsimp only
  let B : ℤ := x^2+3
  let m := 2^(n+1)
  have hB : Odd B := by
    obtain ⟨a, ha⟩ := hx
    refine ⟨2*a^2+1, ?_⟩
    dsimp [B]
    rw [ha]
    ring
  obtain ⟨s, hs, hg⟩ := halfCubic_even_root_to_depth B x hB hx n
  let d := 4*s^2-B
  have hd : Odd d := by
    obtain ⟨b,hb⟩ := hB
    refine ⟨2*s^2-b-1, ?_⟩
    dsimp [d]
    rw [hb]
    ring
  obtain ⟨u, hu, hdu⟩ := odd_inverse_to_depth d hd n
  let a := 3*B*u
  have ha : Odd a := ((by decide : Odd (3 : ℤ)).mul hB).mul hu
  refine ⟨2*s, -s+a, -s-a, even_two_mul _, hs.neg.add_odd ha, ?_, ?_, ?_⟩
  · exact hs.neg.add_odd ha.neg
  · rw [show -s+a-(-s-a)=2*a by ring, Int.mul_ediv_cancel_left _ (by decide)]
    exact ha
  · intro t
    have hg' := cast_dvd m (halfCubic B x s) (by exact_mod_cast hg)
    have hu' := cast_dvd m (d*u-1) (by exact_mod_cast hdu)
    simp only [halfCubic, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hg'
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at hu'
    have hBcast : (B : ZMod m) = (x : ZMod m)^2+3 := by push_cast [B]; rfl
    have hdcast : (d : ZMod m) = 4*(s : ZMod m)^2-(B : ZMod m) := by push_cast [d]; rfl
    have hk := factor_square (x : ZMod m) (s : ZMod m) (u : ZMod m)
      (by rw [← hBcast]; exact hg')
      (by rw [← hBcast, ← hdcast]; exact sub_eq_zero.mp hu')
    rw [← hBcast] at hk
    change _ = (t-((2*s : ℤ) : ZMod m))*(t-((-s+a : ℤ) : ZMod m))*
      (t-((-s-a : ℤ) : ZMod m))
    push_cast
    change _ = (t-2*(s : ZMod m))*(t-(-(s : ZMod m)+(a : ZMod m)))*
      (t-(-(s : ZMod m)-(a : ZMod m)))
    rw [← hBcast]
    change t^3-3*(B : ZMod m)*t+2*(B : ZMod m)*(x : ZMod m) = _
    have ha2 : (a : ZMod m)^2 = 3*(B : ZMod m)-3*(s : ZMod m)^2 := by
      push_cast [a]; exact hk
    rw [show (t-2*(s : ZMod m))*(t-(-(s : ZMod m)+(a : ZMod m)))*
        (t-(-(s : ZMod m)-(a : ZMod m))) =
        (t-2*(s : ZMod m))*((t+(s : ZMod m))^2-(a : ZMod m)^2) by ring, ha2]
    calc
      _ = (t-2*(s : ZMod m))*((t+(s : ZMod m))^2-
          (3*(B : ZMod m)-3*(s : ZMod m)^2)) +
          2*(4*(s : ZMod m)^3-3*(B : ZMod m)*(s : ZMod m)+(B : ZMod m)*(x : ZMod m)) := by ring
      _ = _ := by rw [hg', mul_zero, add_zero]
private theorem cancel_odd (d a : ℤ) (ha : Odd a) (n : ℕ) :
    (2 : ℤ)^n ∣ d*a ↔ (2 : ℤ)^n ∣ d := by
  constructor
  · intro hd
    cases n with
    | zero => simp
    | succ n =>
      obtain ⟨u, _, v, hv⟩ := odd_inverse_to_depth a ha n
      obtain ⟨r, hr⟩ := hd
      refine ⟨r*u-d*v, ?_⟩
      have heq : d = (d*a)*u-d*(a*u-1) := by ring
      nth_rw 1 [heq]
      rw [hr,hv]
      ring
  · intro hd
    exact dvd_mul_of_dvd_left hd a

private theorem odd_half_dichotomy (r p q : ℤ) (hr : Odd r) (hp : Odd p) (hq : Odd q)
    (h : Odd ((p-q)/2)) :
    ∃ a b : ℤ, r-p=2*a ∧ r-q=2*b ∧
      ((Odd a ∧ Even b) ∨ (Even a ∧ Odd b)) := by
  obtain ⟨r', hR⟩ := hr
  obtain ⟨p', hP⟩ := hp
  obtain ⟨q', hQ⟩ := hq
  obtain ⟨w, hw⟩ := h
  refine ⟨r'-p',r'-q',by omega,by omega,?_⟩
  have hdiff : p'-q'=2*w+1 := by omega
  by_cases hA : Even (r'-p')
  · right
    refine ⟨hA,?_⟩
    obtain ⟨a, ha⟩ := hA
    exact ⟨a+w,by omega⟩
  · left
    have ho := Int.not_even_iff_odd.mp hA
    refine ⟨ho,?_⟩
    obtain ⟨a, ha⟩ := ho
    exact ⟨a+w+1,by omega⟩

private theorem product_branches (r e p q : ℤ) (he : Even e) (hp : Odd p) (hq : Odd q)
    (h : Odd ((p-q)/2)) (n : ℕ) :
    (2 : ℤ)^(n+3) ∣ (r-e)*(r-p)*(r-q) ↔
      (2 : ℤ)^(n+3) ∣ (r-e) ∨ (2 : ℤ)^(n+2) ∣ (r-p) ∨ (2 : ℤ)^(n+2) ∣ (r-q) := by
  constructor
  · intro hd
    by_cases hr : Even r
    · exact Or.inl ((cancel_odd _ _ (hr.sub_odd hp) _).mp
        ((cancel_odd _ _ (hr.sub_odd hq) _).mp hd))
    · have ho := Int.not_even_iff_odd.mp hr
      have hodd := ho.sub_even he
      rw [show (r-e)*(r-p)*(r-q)=(r-p)*(r-q)*(r-e) by ring] at hd
      have hf := (cancel_odd _ _ hodd _).mp hd
      obtain ⟨a,b,ha,hb,hab⟩ := odd_half_dichotomy r p q ho hp hq h
      rcases hab with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · rw [show (r-p)*(r-q) = (2*(r-q))*a by rw [ha];ring] at hf
        have h0 := (cancel_odd _ _ ha' _).mp hf
        rw [show (2:ℤ)^(n+3)=2*2^(n+2) by rw [pow_succ,mul_comm]] at h0
        exact Or.inr (Or.inr ((Int.mul_dvd_mul_iff_left (by decide)).mp h0))
      · rw [show (r-p)*(r-q) = (2*(r-p))*b by rw [hb];ring] at hf
        have h0 := (cancel_odd _ _ hb' _).mp hf
        rw [show (2:ℤ)^(n+3)=2*2^(n+2) by rw [pow_succ,mul_comm]] at h0
        exact Or.inr (Or.inl ((Int.mul_dvd_mul_iff_left (by decide)).mp h0))
  · rintro (hE|hP|hQ)
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hE _) _
    · have hp0 : (4 : ℤ) ∣ (r-p) :=
        dvd_trans (show (4:ℤ) ∣ 2^(n+2) by
          simp [pow_add]) hP
      have hr : Odd r := by
        obtain ⟨a,ha⟩ := hp
        obtain ⟨b,hb⟩ := hp0
        exact ⟨a+2*b,by omega⟩
      obtain ⟨j,hj⟩ := hr.sub_odd hq
      obtain ⟨k,hk⟩ := hP
      refine ⟨(r-e)*k*j,?_⟩
      rw [hj,hk,pow_succ]
      ring
    · have hq0 : (4 : ℤ) ∣ (r-q) :=
        dvd_trans (show (4:ℤ) ∣ 2^(n+2) by
          simp [pow_add]) hQ
      have hr : Odd r := by
        obtain ⟨a,ha⟩ := hq
        obtain ⟨b,hb⟩ := hq0
        exact ⟨a+2*b,by omega⟩
      obtain ⟨j,hj⟩ := hr.sub_odd hp
      obtain ⟨k,hk⟩ := hQ
      refine ⟨(r-e)*k*j,?_⟩
      rw [hj,hk,pow_succ]
      ring

/-- Exact full dyadic root locus at precision at least three: one residue
modulo the tested depth and two residues modulo one fewer bit. -/
private theorem real_cubic_dyadic_locus (x : ℤ) (hx : Even x) (n : ℕ) :
    let B : ℤ := x^2+3
    ∃ e p q : ℤ, Even e ∧ Odd p ∧ Odd q ∧ Odd ((p-q)/2) ∧
      ∀ t : ℤ, (2 : ℤ)^(n+3) ∣ (t^3-3*B*t+2*B*x) ↔
        (2 : ℤ)^(n+3) ∣ (t-e) ∨
        (2 : ℤ)^(n+2) ∣ (t-p) ∨ (2 : ℤ)^(n+2) ∣ (t-q) := by
  obtain ⟨e,p,q,he,hp,hq,hd,hfac⟩ := real_cubic_dyadic_split x hx (n+2)
  refine ⟨e,p,q,he,hp,hq,hd,fun t => ?_⟩
  let m : ℕ := 2^(n+3)
  have hf := hfac (t : ZMod m)
  have base : (((t^3-3*(x^2+3)*t+2*(x^2+3)*x : ℤ) : ZMod m)) =
      ((((t-e)*(t-p)*(t-q) : ℤ) : ZMod m)) := by
    push_cast
    push_cast at hf
    exact hf
  have hI : (2:ℤ)^(n+3) ∣ (t^3-3*(x^2+3)*t+2*(x^2+3)*x) ↔
      (2:ℤ)^(n+3) ∣ (t-e)*(t-p)*(t-q) := by
    have hl := ZMod.intCast_zmod_eq_zero_iff_dvd (t^3-3*(x^2+3)*t+2*(x^2+3)*x) m
    have hr := ZMod.intCast_zmod_eq_zero_iff_dvd ((t-e)*(t-p)*(t-q)) m
    rw [base] at hl
    exact_mod_cast hl.symm.trans hr
  exact hI.trans (product_branches t e p q he hp hq hd n)

/-- The actual rational Cardano residual at dyadic precision n+3. -/
def nativeResidual (n j : ℕ) (t : ℤ) : ℤ :=
  let x := goldenLucas (3^j)
  let B := x^2+3
  (t^3-3*B*t+2*B*x) % (2:ℤ)^(n+3)

/-- For each positive native Lucas level and precision at least three,
one full-width residue and two half-width odd classes are all the roots. -/
theorem native_cubic_dyadic_locus (n : ℕ) :
    let residual := nativeResidual n
    ∀ (j : ℕ) (_hj : 1 ≤ j),
      ∃ e p q : ℤ, Even e ∧ Odd p ∧ Odd q ∧ Odd ((p-q)/2) ∧
        ∀ t : ℤ, residual j t = 0 ↔
          (2 : ℤ)^(n+3) ∣ (t-e) ∨
          (2 : ℤ)^(n+2) ∣ (t-p) ∨ (2 : ℤ)^(n+2) ∣ (t-q) := by
  intro residual j hj
  have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2))
    (golden_cubic_lucas_block j hj).1
  have hh : ((goldenLucas (3^j) : ℤ) : ZMod 2) = 0 := by
    simp only [map_intCast, map_ofNat] at h
    rw [show (4 : ZMod 2) = 0 by decide] at h
    exact h
  have he : Even (goldenLucas (3^j)) := even_iff_two_dvd.mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  obtain ⟨e,p,q,he,hp,hq,hd,hf⟩ := real_cubic_dyadic_locus _ he n
  refine ⟨e,p,q,he,hp,hq,hd,fun t => ?_⟩
  change ((t^3-3*(goldenLucas (3^j)^2+3)*t+
      2*(goldenLucas (3^j)^2+3)*goldenLucas (3^j)) % (2:ℤ)^(n+3) = 0) ↔ _
  exact Int.dvd_iff_emod_eq_zero.symm.trans (hf t)
end D5.S3.Arith.Primes.GoldenCubicDyadicRootLocus
