/- GID: D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The mirror-step ruin probability has Martinez's conjectured limit. -/

/-
admission_basis: open-problem-resolution (#19080; Proved)
escape_witness: none
Direct frozen dependencies: none (only pinned Mathlib imports).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19149.
Utility none: arbitrary real parameters, with no bounded enumeration, checker,
numeric reduction premises or certified finite instance.

Definitions IsWinProbability, limitValue and claim give the source recurrence and limit.
Private definition solution constructs the finite solution.
The reciprocal root is written inline; upperDiag in ActualPureQubitGeometry
already supplies an affine quadratic-root expression.
root_facts: proof_shape: bind-only; consumers: constants; escape_witness: none.
constants: proof_shape: bind-only; consumers: result; escape_witness: none.
finite_solution: proof_shape: bind-only; consumers: result; escape_witness: none.
harmonic_nonpos: proof_shape: content; consumers: harmonic_unique; escape_witness: none.
harmonic_unique: proof_shape: content; consumers: result; escape_witness: none.
solution_limit: proof_shape: bind-only; consumers: result; escape_witness: none.
limit_identity: proof_shape: bind-only; consumers: result; escape_witness: none.
result: proof_shape: content; escape_witness: none.
The maximum descent supplies the non-normalization step after helper inlining.
The finite formula and coefficient construction allow arbitrary positive a,b,c summing to one;
uniqueness allows b,c nonnegative and requires only a positive.
-/


import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.QuadraticDiscriminant

/-! Binding conventions for L. Martinez, "A symbolic computational approach to the generalized gambler's
ruin problem in one and two dimensions", arXiv:2412.07667v1, Section 4 (the mirror step) and
Conjecture 5.1. -/

namespace D5.S3.Combinatorics.Probability.MartinezMirrorGamblersRuin

/-- Section 4 and Conjecture 5.1: on `{0, …, N}`, from an interior point `0 < x < N` the particle moves to
`x − 1` with probability `q₁ = (1 − p)/2`, to `x + 1` with probability `p`, and to `N − x` (the mirror
step) with probability `q₂ = (1 − p)/2`, until it reaches `0` or `N`. The probability `f_N^{(p)}(x)` of
ending at `N` satisfies the first-step recurrence with `f(0) = 0` and `f(N) = 1`. -/
def IsWinProbability (p : ℝ) (N : ℕ) (f : ℕ → ℝ) : Prop :=
  f 0 = 0 ∧ f N = 1 ∧ ∀ x, 0 < x → x < N →
    f x = (1 - p) / 2 * f (x - 1) + p * f (x + 1) + (1 - p) / 2 * f (N - x)

/-- Conjecture 5.1: the conjectured value
`(√((p + 1)(1 − 3p + 4p²)) − (1 − 2p)(p + 1)) / (2p(p + 1))`. -/
noncomputable def limitValue (p : ℝ) : ℝ :=
  (Real.sqrt ((p + 1) * (1 - 3 * p + 4 * p ^ 2)) - (1 - 2 * p) * (p + 1)) / (2 * p * (p + 1))

/-- Conjecture 5.1: "If the particle starts at `x = 1`, then `lim_{N→∞} f_N^{(p)}(1)` equals" the value
above, for every `0 < p < 1`. -/
def claim : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∀ f : ℕ → ℕ → ℝ, (∀ N, 2 ≤ N → IsWinProbability p N (f N)) →
    Filter.Tendsto (fun N => f N 1) Filter.atTop (nhds (limitValue p))


private theorem root_facts (T : ℝ) (hT : 2 < T) :
    0 < (T - Real.sqrt (T^2-4))/2 ∧ (T - Real.sqrt (T^2-4))/2 < 1 ∧
      ((T - Real.sqrt (T^2-4))/2) ^ 2 - T * ((T - Real.sqrt (T^2-4))/2) + 1 = 0 := by
  have hD : 0 ≤ T^2-4 := by nlinarith
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg (T^2-4)
  have hsT : Real.sqrt (T^2-4) < T :=
    (Real.sqrt_lt' (by linarith : 0 < T)).2 (by linarith)
  have hsL : T-2 < Real.sqrt (T^2-4) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

private theorem constants (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a+b+c=1) :
    ∃ r R : ℝ, 0 < r ∧ r < 1 ∧ R < 0 ∧
      a*b*r^2 - (a+b-2*a*b)*r + a*b = 0 ∧
      1 = a / r + b*r + c*R ∧ R = a*R*r + b*R/r + c := by
  let T := (a+b)/(a*b)-2
  have hab : 0 < a*b := mul_pos ha hb
  have hs : 0 < a+b := add_pos ha hb
  have hs1 : a+b < 1 := by linarith
  have hab4 : 4*a*b ≤ (a+b)^2 := four_mul_le_pow_two_add a b
  have hT : 2 < T := by
    dsimp [T]
    have : 4 < (a+b)/(a*b) := (lt_div_iff₀ hab).2 (by nlinarith)
    linarith
  obtain ⟨hr0,hr1,hq⟩ := root_facts T hT
  let r := (T - Real.sqrt (T^2-4))/2
  change 0 < r at hr0
  change r < 1 at hr1
  change r^2-T*r+1=0 at hq
  have hr : r ≠ 0 := ne_of_gt hr0
  have hrt : r + 1/r = T := by
    field_simp
    nlinarith [hq]
  let K₁ := 1-a/r-b*r
  let K₂ := 1-a*r-b/r
  have hpoly : a*b*r^2 - (a+b-2*a*b)*r + a*b = 0 := by
    have hrel : T*(a*b)=a+b-2*a*b := by dsimp [T]; field_simp
    linear_combination (a*b)*hq + r*hrel
  have hK : K₁*K₂=c^2 := by
    dsimp [K₁,K₂]
    rw [show c=1-a-b by linarith]
    field_simp
    linear_combination (r^2-2*r+1)*hpoly
  have hsum : K₁+K₂ < 0 := by
    have heq : K₁+K₂ = 2-(a+b)*T := by dsimp [K₁,K₂]; rw [← hrt]; ring
    rw [heq]
    have hh : 2 < (a+b)*T := by
      dsimp [T]
      have he : 4 ≤ (a+b)^2/(a*b) := (le_div_iff₀ hab).2 (by nlinarith only [hab4])
      have hrewrite : (a+b)*((a+b)/(a*b)-2)=(a+b)^2/(a*b)-2*(a+b) := by ring
      rw [hrewrite]
      linarith
    linarith
  have hKneg : K₁ < 0 := by
    by_contra h
    have hKnonneg : 0 ≤ K₁ := le_of_not_gt h
    have hK₂neg : K₂ < 0 := lt_of_add_lt_of_nonneg_right hsum hKnonneg
    have : K₁*K₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKnonneg hK₂neg.le
    nlinarith [sq_pos_of_pos hc]
  refine ⟨r,K₁/c,hr0,hr1,div_neg_of_neg_of_pos hKneg hc,hpoly,?_,?_⟩
  · dsimp [K₁]; field_simp; ring
  · have hc0 := ne_of_gt hc
    dsimp [K₂] at hK
    field_simp [hr,hc0] at hK ⊢
    nlinarith [hK]


private noncomputable def solution (r R : ℝ) (N x : ℕ) : ℝ :=
  (1-r^x)*(1-R*r^(N-x))/((1-R)*(1-r^N))

private theorem finite_solution (a b c r R : ℝ) (habc : a+b+c=1)
    (hr0 : 0 < r) (hr1 : r < 1) (hR : R < 0)
    (hK₁ : 1 = a/r+b*r+c*R) (hK₂ : R = a*R*r+b*R/r+c)
    (N : ℕ) (hN : 0 < N) :
    solution r R N 0 = 0 ∧ solution r R N N = 1 ∧
    ∀ x, 0 < x → x < N → solution r R N x =
      a*solution r R N (x-1)+b*solution r R N (x+1)+c*solution r R N (N-x) := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have hD : (1-R)*(1-r^N) ≠ 0 := by
    apply mul_ne_zero
    · linarith
    · have := pow_lt_one₀ hr0.le hr1 (Nat.ne_of_gt hN)
      linarith
  constructor
  · simp [solution]
  constructor
  · simp only [solution, Nat.sub_self, pow_zero]
    simpa only [mul_one, mul_comm] using div_self hD
  intro x hx hxN
  have hxle : x ≤ N := hxN.le
  have hxm : r^(x-1)*r = r^x := pow_sub_one_mul (Nat.ne_of_gt hx) r
  have hxp : r^(x+1) = r^x*r := pow_succ _ _
  have hNm : r^(N-(x-1)) = r^(N-x)*r := by rw [← pow_succ]; congr 1; omega
  have hNp : r^(N-(x+1))*r = r^(N-x) := by
    simpa only [Nat.sub_sub] using (pow_sub_one_mul (by omega : N-x ≠ 0) r)
  have hNx : N-(N-x)=x := Nat.sub_sub_self hxle
  have hprod : r^x*r^(N-x) = r^N := pow_mul_pow_sub r hxle
  have hprodm : r^(x-1)*r^(N-(x-1)) = r^N :=
    pow_mul_pow_sub r ((Nat.sub_le x 1).trans hxle)
  have hprodp : r^(x+1)*r^(N-(x+1)) = r^N := pow_mul_pow_sub r hxN
  have hp1 : a+b*r^2+c*R*r = r := by
    field_simp [hr] at hK₁
    nlinarith [hK₁]
  have hp2 : a*R*r^2+b*R+c*r = R*r := by
    field_simp [hr] at hK₂
    nlinarith [hK₂]
  have he1 : a*r^(x-1)+b*r^(x+1)+c*R*r^x=r^x := by
    calc
      _ = (a+b*r^2+c*R*r)*r^(x-1) := by rw [hxp, ← hxm]; ring
      _ = _ := by rw [hp1]; linarith [hxm]
  have he2 : a*R*r^(N-(x-1))+b*R*r^(N-(x+1))+c*r^(N-x)=R*r^(N-x) := by
    calc
      _ = (a*R*r^2+b*R+c*r)*r^(N-(x+1)) := by rw [hNm, ← hNp]; ring
      _ = _ := by rw [hp2]; linear_combination R*hNp
  have hnum : (1-r^x)*(1-R*r^(N-x)) =
      a*((1-r^(x-1))*(1-R*r^(N-(x-1)))) +
      b*((1-r^(x+1))*(1-R*r^(N-(x+1)))) +
      c*((1-r^(N-x))*(1-R*r^x)) := by
    linear_combination he1 + he2 - (1+R*r^N)*habc +
      R*hprod - a*R*hprodm - b*R*hprodp - c*R*hprod
  dsimp [solution]
  rw [hNx]
  rw [hnum]
  ring


private theorem harmonic_nonpos (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a+b+c=1) (N : ℕ) (f : ℕ → ℝ) (h0 : f 0=0) (hn : f N=0)
    (hh : ∀ x, 0 < x → x < N → f x=a*f (x-1)+b*f (x+1)+c*f (N-x)) :
    ∀ x, x ≤ N → f x ≤ 0 := by
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image (Finset.range (N+1)) f ⟨0,by simp⟩
  have hbound : ∀ k, k ≤ N → f k ≤ f m := fun k hk => hmax k (by simp; omega)
  have hdesc : ∀ k, k ≤ N → f k=f m → f m=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk he
      by_cases hk0 : k=0
      · simpa [hk0,h0] using he.symm
      by_cases hkN : k=N
      · simpa [hkN,hn] using he.symm
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hklt : k < N := Nat.lt_of_le_of_ne hk hkN
      have hleft := hbound (k-1) (by omega)
      have hright := hbound (k+1) (by omega)
      have hmirror := hbound (N-k) (by omega)
      have hav := hh k hkpos hklt
      have hbudget : a*f m+b*f m+c*f m=f m := by
        calc
          _ = (a+b+c)*f m := by ring
          _ = _ := by rw [habc,one_mul]
      have hlefteq : f (k-1)=f m := by
        have hbr := mul_nonneg hb (sub_nonneg.mpr hright)
        have hcm := mul_nonneg hc (sub_nonneg.mpr hmirror)
        have hprod : a*(f m-f (k-1)) ≤ 0 := by rw [he] at hav; nlinarith only [hav,hbudget,hbr,hcm]
        nlinarith only [hprod,ha,hleft]
      exact ih (k-1) (by omega) (by omega) hlefteq
  have hM : f m=0 := hdesc m (by simpa using hm) rfl
  intro x hx
  simpa [hM] using hbound x hx

private theorem harmonic_unique (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a+b+c=1) (N : ℕ) (f g : ℕ → ℝ) (h0 : f 0=g 0) (hn : f N=g N)
    (hf : ∀ x, 0 < x → x < N → f x=a*f (x-1)+b*f (x+1)+c*f (N-x))
    (hg : ∀ x, 0 < x → x < N → g x=a*g (x-1)+b*g (x+1)+c*g (N-x)) :
    ∀ x, x ≤ N → f x=g x := by
  have aux (u v : ℕ → ℝ) (huv0 : u 0=v 0) (huvn : u N=v N)
      (hu : ∀ x, 0 < x → x < N → u x=a*u (x-1)+b*u (x+1)+c*u (N-x))
      (hv : ∀ x, 0 < x → x < N → v x=a*v (x-1)+b*v (x+1)+c*v (N-x)) :
      ∀ x, x ≤ N → u x-v x ≤ 0 := by
    apply harmonic_nonpos a b c ha hb hc habc N (fun x => u x-v x)
    · simp [huv0]
    · simp [huvn]
    · intro x hx hxN
      rw [hu x hx hxN,hv x hx hxN]
      ring
  intro x hx
  have hh₁ := aux f g h0 hn hf hg x hx
  have hh₂ := aux g f h0.symm hn.symm hg hf x hx
  linarith

private theorem solution_limit (r R : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hR : R < 0) :
    Filter.Tendsto (fun N => solution r R N 1) Filter.atTop (nhds ((1-r)/(1-R))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hs := hp.comp (Filter.tendsto_sub_atTop_nat 1)
  have hnum : Filter.Tendsto (fun N : ℕ => (1-r)*(1-R*r^(N-1))) Filter.atTop
      (nhds ((1-r)*(1-R*0))) :=
    (tendsto_const_nhds.sub (hs.const_mul R)).const_mul (1-r)
  have hden : Filter.Tendsto (fun N : ℕ => (1-R)*(1-r^N)) Filter.atTop
      (nhds ((1-R)*(1-0))) := (tendsto_const_nhds.sub hp).const_mul (1-R)
  have hne : (1-R)*(1-(0:ℝ)) ≠ 0 := by simpa using (ne_of_gt (show 0 < 1-R by linarith))
  simpa only [Pi.div_def, solution, pow_one, mul_zero, sub_zero, mul_one] using hnum.div hden hne

private theorem limit_identity (p r R : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hR : R < 0)
    (hq : ((1-p)/2)*p*r^2 - ((1-p)/2+p-2*((1-p)/2)*p)*r + ((1-p)/2)*p=0)
    (hK : 1 = ((1-p)/2)/r+p*r+((1-p)/2)*R) :
    (1-r)/(1-R) = limitValue p := by
  let a := (1-p)/2
  let L := (1-r)/(1-R)
  have ha : 0 < a := by dsimp [a]; linarith
  have hLpos : 0 < L := div_pos (by linarith) (by linarith)
  have hL : L*(1-R)=1-r := div_mul_cancel₀ _ (by linarith : 1-R ≠ 0)
  have he : r-a-p*r^2-a*R*r=0 := by
    dsimp [a]
    field_simp [hr0.ne'] at hK
    nlinarith only [hK]
  have hLin : (a+p*L)*r=a*L := by
    have hh : (1-r)*((a+p*L)*r-a*L)=0 := by
      dsimp [a] at *
      linear_combination L*he - ((1-p)/2)*r*hL
    have : (a+p*L)*r-a*L=0 := (mul_eq_zero.mp hh).resolve_left (by linarith)
    linarith
  have hd : a+p*L ≠ 0 := ne_of_gt (add_pos ha (mul_pos hp hLpos))
  have hrEq : r=a*L/(a+p*L) := (eq_div_iff hd).2 (by simpa [mul_comm] using hLin)
  have hpoly : p*(p+1)*L^2+(1-2*p)*(p+1)*L-p*(1-p)=0 := by
    have hq' := hq
    change a*p*r^2-(a+p-2*a*p)*r+a*p=0 at hq'
    rw [hrEq] at hq'
    field_simp [hd] at hq'
    have hh : (1-p)^2*(p*(p+1)*L^2+(1-2*p)*(p+1)*L-p*(1-p))=0 := by
      dsimp [a] at hq'
      linear_combination -8*hq'
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (by linarith))
  let A := p*(p+1)
  let B := (1-2*p)*(p+1)
  let D := (p+1)*(1-3*p+4*p^2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < p*(1-p) := mul_pos hp (by linarith)
  have hsq : (2*A*L+B)^2=D := by
    have hquadratic : A*(L*L)+B*L+(-p*(1-p))=0 := by
      dsimp [A,B]
      nlinarith only [hpoly]
    have hdiscrim := discrim_eq_sq_of_quadratic_eq_zero hquadratic
    dsimp [discrim,A,B,D] at hdiscrim ⊢
    nlinarith only [hdiscrim]
  have hS : 0 < 2*A*L+B := by
    change A*L^2+B*L-p*(1-p)=0 at hpoly
    by_contra h
    have hh : 2*A*L+B ≤ 0 := le_of_not_gt h
    have hh' : L*(2*A*L+B) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hLpos.le hh
    nlinarith [mul_pos hA (sq_pos_of_pos hLpos)]
  have hsqrt : Real.sqrt D=2*A*L+B := by
    rw [← hsq,Real.sqrt_sq hS.le]
  dsimp [limitValue]
  change L=(Real.sqrt D-B)/(2*p*(p+1))
  rw [show 2*p*(p+1)=2*A by dsimp [A]; ring]
  rw [hsqrt]
  field_simp
  ring


theorem result : claim := by
  intro p hp hp1 f hf
  let a := (1-p)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have habc : a+p+a=1 := by dsimp [a]; ring
  obtain ⟨r,R,hr0,hr1,hR,hq,hK1,hK2⟩ := constants a p a ha hp ha habc
  have hlim := solution_limit r R hr0 hr1 hR
  rw [limit_identity p r R hp hp1 hr0 hr1 hR hq hK1] at hlim
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have hprob := hf N hN
  have hsol := finite_solution a p a r R habc hr0 hr1 hR hK1 hK2 N (by omega)
  exact (harmonic_unique a p a ha hp.le ha.le habc N (f N) (solution r R N)
    (hprob.1.trans hsol.1.symm) (hprob.2.1.trans hsol.2.1.symm)
    hprob.2.2 hsol.2.2 1 (by omega)).symm


end D5.S3.Combinatorics.Probability.MartinezMirrorGamblersRuin
