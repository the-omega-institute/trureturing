/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumJet
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential sum positivity from polynomial initial values. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetEvaluation
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetBounds
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetMask

/-! A one-parameter annihilating chain with integer-polynomial weights.
The coefficient variable is x = p - 1, and the rate of b^i y^j is -(8i+jp).
Only integer evaluations of the groups enter the executable mask sweep. -/

open scoped BigOperators
open Polynomial

namespace RefinedBMV.ZeroSpectrum

open DividedDifference.SparseExpansion

structure Group where
  bPower : ℕ
  yPower : ℕ
  coefficients : List (ℕ × ℤ)

def Group.rate (g : Group) : Rate := (8 * g.bPower, g.yPower)

def Group.weight {R : Type*} [CommRing R] (x : R) (g : Group) : R :=
  (g.coefficients.map fun a => (a.2 : R) * x^a.1).sum

def Group.eval {R : Type*} [CommRing R] (x b y : R) (g : Group) : R :=
  g.weight x * b^g.bPower * y^g.yPower

def evalGroups {R : Type*} [CommRing R] (x b y : R) (gs : List Group) : R :=
  (gs.map (Group.eval x b y)).sum

noncomputable def Group.poly (g : Group) : ℤ[X] :=
  (g.coefficients.map fun a => monomial a.1 a.2).sum

def Group.mass (g : Group) : ℤ := (g.coefficients.map fun a => |a.2|).sum

def mass (gs : List Group) : ℤ := (gs.map Group.mass).sum

def difference (root a : Rate) : ℤ × ℤ :=
  (((root.1 : ℤ) + root.2) - ((a.1 : ℤ) + a.2), (root.2 : ℤ) - a.2)

noncomputable def factor (a : Rate) (roots : List Rate) : ℤ[X] :=
  (roots.map fun r => Rate.shifted r - Rate.shifted a).prod

noncomputable def jet (gs : List Group) (roots : List Rate) : ℤ[X] :=
  (gs.map fun g => g.poly * factor g.rate roots).sum

private theorem sum_get {T S : Type*} [AddCommMonoid S] (xs : List T) (f : T → S) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  rw [← List.sum_ofFn, ← List.ofFn_getElem (xs := xs)]
  simp

private theorem shifted_sub (r a : Rate) :
    Rate.shifted r - Rate.shifted a =
      C (difference r a).1 + C (difference r a).2 * X := by
  simp only [Rate.shifted, difference, map_sub]
  ring

private theorem eval₂_weight (g : Group) (x : ℝ) :
    g.poly.eval₂ (Int.castRingHom ℝ) x = g.weight x := by
  simp [Group.poly, Group.weight, Polynomial.eval₂_list_sum, Polynomial.eval₂_monomial,
    List.map_map, Function.comp_def]

private theorem eval_weight (g : Group) (x : ℤ) :
    g.poly.eval x = g.weight x := by
  simp [Group.poly, Group.weight, Polynomial.eval_listSum, Polynomial.eval_monomial,
    List.map_map, Function.comp_def]

private theorem eval₂_factor (a : Rate) (roots : List Rate) (p : ℝ) :
    (factor a roots).eval₂ (Int.castRingHom ℝ) (p - 1) =
      (roots.map fun r => Rate.atP r p - Rate.atP a p).prod := by
  induction roots with
  | nil => simp [factor]
  | cons r rs ih =>
    simp only [factor, List.map_cons, List.prod_cons, Polynomial.eval₂_mul,
      Polynomial.eval₂_sub, shifted_rate_eval] at ih ⊢
    rw [ih]

private theorem eval₂_jet (gs : List Group) (roots : List Rate) (p : ℝ) :
    (jet gs roots).eval₂ (Int.castRingHom ℝ) (p - 1) =
      (gs.map fun g => g.weight (p - 1) *
        (roots.map fun r => Rate.atP r p - Rate.atP g.rate p).prod).sum := by
  induction gs with
  | nil => simp [jet]
  | cons g gs ih =>
    simp only [jet, List.map_cons, List.sum_cons, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      eval₂_weight, eval₂_factor] at ih ⊢
    rw [ih]

/-- The second variable of the library's mixed-prefix criterion is constant zero. -/
theorem nonneg_of_jets (gs : List Group)
    (hjet : ∀ k < gs.length, ∀ x : ℝ, 0 ≤ x →
      0 ≤ (jet gs ((gs.map Group.rate).take k)).eval₂ (Int.castRingHom ℝ) x)
    (p t : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    0 ≤ evalGroups (p-1) (Real.exp (-8*t)) (Real.exp (-p*t)) gs := by
  let rate (i : Fin gs.length) := -Rate.atP (gs.get i).rate p
  let roots := (gs.map Group.rate).map fun r => -Rate.atP r p
  let w (i : Fin gs.length) := (gs.get i).weight (p - 1)
  have hr (i : Fin gs.length) : rate i ∈ roots :=
    List.mem_map.mpr ⟨(gs.get i).rate,
      List.mem_map.mpr ⟨gs.get i, List.get_mem gs i, rfl⟩, rfl⟩
  have hprefix (k : ℕ) (hk : k < roots.length) (l : ℕ) (hl : l < ([0] : List ℝ).length) :
      0 ≤ ∑ i : Fin gs.length, w i * ExponentialChain.factors (roots.take k) (rate i) *
        ExponentialChain.factors (([0] : List ℝ).take l) 0 := by
    have hl0 : l = 0 := by simpa using hl
    subst l
    have h := hjet k (by simpa [roots] using hk) (p - 1) (sub_nonneg.mpr hp)
    rw [eval₂_jet] at h
    simp only [ExponentialChain.factors, List.take_zero, List.map_nil, List.prod_nil, mul_one,
      w, rate, roots, ← List.map_take, List.map_map, Function.comp_def, neg_sub_neg]
    rw [sum_get gs (fun g => g.weight (p - 1) *
      ((gs.take k).map fun r => Rate.atP r.rate p - Rate.atP g.rate p).prod)]
    simpa only [← List.map_take, List.map_map, Function.comp_def] using h
  have h := ExponentialChain.termwise_sum_nonneg_of_mixed_prefix
    rate (fun _ => 0) roots [0] hr (fun _ => by simp) w hprefix t 0 ht le_rfl
  simp only [zero_mul, add_zero, w, rate] at h
  rw [sum_get gs (fun g => g.weight (p - 1) *
    Real.exp (-Rate.atP g.rate p * t))] at h
  unfold evalGroups
  convert h using 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro g _
  unfold Group.eval
  have he : (Real.exp (-8*t))^g.bPower * (Real.exp (-p*t))^g.yPower =
      Real.exp (-Rate.atP g.rate p * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold Group.rate Rate.atP
    push_cast
    ring
  rw [mul_assoc, he]

private theorem poly_bounds (gs : List Group) (d : ℕ)
    (h : ∀ g ∈ gs, ∀ a ∈ g.coefficients, a.1 ≤ d) :
    ∀ g ∈ gs, (∀ j, |g.poly.coeff j| ≤ g.mass) ∧ g.poly.natDegree ≤ d := by
  intro g hg
  have hb := JetBounds.sum_bounds (Finset.univ : Finset (Fin g.coefficients.length))
    (fun i => monomial (g.coefficients.get i).1 (g.coefficients.get i).2)
    (fun i => |(g.coefficients.get i).2|) d (by
      intro i _
      constructor
      · intro j
        rw [coeff_monomial]
        split <;> simp
      · exact (natDegree_monomial_le _).trans (h g hg _ (List.get_mem _ i)))
  rw [sum_get g.coefficients (fun a => monomial a.1 a.2),
      sum_get g.coefficients (fun a => |a.2|)] at hb
  exact hb

private theorem factor_degree (a : Rate) (rs : List Rate) :
    (factor a rs).natDegree ≤ rs.length := by
  induction rs with
  | nil => simp [factor]
  | cons r rs ih =>
    have hr : (Rate.shifted r - Rate.shifted a).natDegree ≤ 1 := by
      rw [shifted_sub]
      apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    simpa [factor, Nat.add_comm 1] using natDegree_mul_le_of_le hr ih

private theorem jet_bounds (gs : List Group) (rs : List Rate) (n d : ℕ) (B : ℤ)
    (hd : ∀ g ∈ gs, ∀ a ∈ g.coefficients, a.1 ≤ d)
    (hB : 1 ≤ B) (hlen : rs.length ≤ n)
    (hfactor : ∀ g ∈ gs, ∀ r ∈ rs, |(difference r g.rate).1| + |(difference r g.rate).2| ≤ B) :
    (∀ j, |(jet gs rs).coeff j| ≤ mass gs * B^n) ∧
      (jet gs rs).natDegree ≤ d+n := by
  have hb := JetBounds.sum_bounds (Finset.univ : Finset (Fin gs.length))
    (fun i => (gs.get i).poly * factor (gs.get i).rate rs)
    (fun i => (gs.get i).mass * B^n) (d+n) (by
      intro i _
      let g := gs.get i
      have hg : g ∈ gs := List.get_mem gs i
      obtain ⟨hc, hdeg⟩ := poly_bounds gs d hd g hg
      have hmass : 0 ≤ g.mass := by
        unfold Group.mass
        exact List.sum_nonneg fun z hz => by
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
          exact abs_nonneg a.2
      have heq : factor g.rate rs =
          ((rs.map fun r => difference r g.rate).map fun a => C a.1 + C a.2 * X).prod := by
        simp [factor, shifted_sub, List.map_map, Function.comp_def]
      constructor
      · intro j
        change |(g.poly * factor g.rate rs).coeff j| ≤ g.mass * B^n
        rw [mul_comm, heq]
        have h := JetBounds.coeff_abs_affine_chain (rs.map fun r => difference r g.rate)
          g.poly g.mass B hmass (by omega) (by
            intro a ha
            obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
            exact hfactor g hg r hr) hc j
        simp only [List.length_map] at h
        exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hlen) hmass)
      · exact natDegree_mul_le_of_le hdeg ((factor_degree g.rate rs).trans hlen))
  rw [sum_get gs (fun g => g.poly * factor g.rate rs),
      sum_get gs (fun g => g.mass * B^n)] at hb
  rw [List.sum_map_mul_right] at hb
  exact hb

/-- Packed evaluation of a rate, with variable x = p - 1. -/
def rateInt (base : ℤ) (a : Rate) : ℤ := (a.1 : ℤ) + a.2 * (1 + base)

private def factorInt (base : ℤ) (a : Rate) (rs : List Rate) : ℤ :=
  (rs.map fun r => rateInt base r - rateInt base a).prod

private theorem eval_factor_int (base : ℤ) (a : Rate) (rs : List Rate) :
    (factor a rs).eval base = factorInt base a rs := by
  have hr (a : Rate) : (Rate.shifted a).eval base = rateInt base a := by
    simp [Rate.shifted, rateInt, Polynomial.eval_add, Polynomial.eval_mul]
    ring
  simp [factor, factorInt, Polynomial.eval_list_prod, Polynomial.eval_sub,
    List.map_map, Function.comp_def, hr]

private theorem eval_jet_int (base : ℤ) (gs : List Group) (rs : List Rate) :
    (jet gs rs).eval base =
      (gs.map fun g => g.weight base * factorInt base g.rate rs).sum := by
  induction gs with
  | nil => simp [jet]
  | cons g gs ih =>
    simp only [jet, List.map_cons, List.sum_cons, Polynomial.eval_add, Polynomial.eval_mul,
      eval_weight, eval_factor_int] at ih ⊢
    rw [ih]

/-- The grouped integer recurrence is the one-variable version of ThreeSpectrum.GroupedMasks. -/
private def step (base : ℤ) (a : Rate) (tail : List (Rate × ℤ)) : List (Rate × ℤ) :=
  tail.map fun (r,v) => (r, v * (rateInt base a - rateInt base r))

private def sweep (base : ℤ) (test : ℤ → Bool) : ℕ → List (Rate × ℤ) → Bool
  | 0, _ => true
  | _+1, [] => true
  | n+1, (a,w)::tail =>
      test (w + (tail.map Prod.snd).sum) && sweep base test n (step base a tail)

private def prefixMoment (base : ℤ) (ws : List (Rate × ℤ)) (j : ℕ) : ℤ :=
  (ws.map fun (r,v) => v * factorInt base r ((ws.map Prod.fst).take j)).sum

private theorem sweep_sound (base : ℤ) (test : ℤ → Bool) (n : ℕ) (ws : List (Rate × ℤ))
    (h : sweep base test n ws = true) (j : ℕ) (hj : j < min n ws.length) :
    test (prefixMoment base ws j) = true := by
  induction n generalizing ws j with
  | zero => simp at hj
  | succ n ih =>
    cases ws with
    | nil => simp at hj
    | cons a tail =>
      obtain ⟨r,w⟩ := a
      have hh : (test (w + (tail.map Prod.snd).sum) &&
          sweep base test n (step base r tail)) = true := h
      simp only [Bool.and_eq_true] at hh
      obtain ⟨hhead, htail⟩ := hh
      cases j with
      | zero =>
        simpa [prefixMoment, factorInt] using hhead
      | succ j =>
        have hj' : j < min n (step base r tail).length := by
          simp [step] at hj ⊢
          omega
        have heq : prefixMoment base ((r,w)::tail) (j+1) =
            prefixMoment base (step base r tail) j := by
          simp only [prefixMoment, factorInt, List.map_cons, List.take_succ_cons, List.prod_cons,
            List.sum_cons, sub_self, zero_mul, mul_zero, zero_add, step, List.map_map,
            Function.comp_def]
          congr 1
          apply List.map_congr_left
          rintro ⟨a,v⟩ _
          simp [mul_assoc]
        rw [heq]
        exact ih _ htail _ hj'

def masked (width digits : ℕ) (v : ℤ) : Bool :=
  let m := DimThree.PackedCheck.polynomialMask width digits
  ((v + (m : ℤ)).toNat &&& m) == m

def checkMasks (width digits : ℕ) (gs : List Group) : Bool :=
  let base : ℤ := 2^(width+1)
  sweep base (masked width digits) gs.length (gs.map fun g => (g.rate,g.weight base))

/-- Static checks guard degree and coefficient bounds in the packed sign interpretation. -/
def staticCheck (gs : List Group) (d : ℕ) (B : ℤ) (width digits : ℕ) : Bool :=
  decide (1 ≤ B ∧ d + gs.length ≤ digits ∧ mass gs * B^gs.length < (2 : ℤ)^width) &&
    gs.all (fun g => g.coefficients.all fun a => decide (a.1 ≤ d)) &&
    gs.all (fun g => gs.all fun r =>
      decide (|(difference r.rate g.rate).1| + |(difference r.rate g.rate).2| ≤ B))

theorem nonneg_of_checks (gs : List Group) (d : ℕ) (B : ℤ) (width digits : ℕ)
    (hstatic : staticCheck gs d B width digits = true)
    (hmask : checkMasks width digits gs = true)
    (p t : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    0 ≤ evalGroups (p-1) (Real.exp (-8*t)) (Real.exp (-p*t)) gs := by
  simp only [staticCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hstatic
  obtain ⟨⟨⟨hB, hdigit, hsmall⟩, hd⟩, hfactor⟩ := hstatic
  apply nonneg_of_jets gs _ p t hp ht
  intro k hk x hx
  let rs := (gs.map Group.rate).take k
  have hlen : rs.length ≤ gs.length := by simp [rs]
  obtain ⟨hc, hdeg⟩ := jet_bounds gs rs gs.length d B hd hB hlen (by
    intro g hg r hr
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hr)
    exact hfactor g hg a ha)
  have hlen' : rs.length ≤ k := by simp [rs]
  have hdegree : (jet gs rs).natDegree < digits := by
    have hd' := (jet_bounds gs rs k d B hd hB hlen' (by
      intro g hg r hr
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hr)
      exact hfactor g hg a ha)).2
    omega
  let radix : ℤ := 2^(width+1)
  let weighted := gs.map fun g => (g.rate, g.weight radix)
  have hmask' : sweep radix (masked width digits) gs.length weighted = true := by
    simpa only [radix, weighted, checkMasks] using hmask
  have hm := sweep_sound radix (masked width digits) gs.length weighted hmask' k (by
    simpa [weighted] using hk)
  have he : prefixMoment (2^(width+1) : ℤ)
      (gs.map fun g => (g.rate,g.weight (2^(width+1)))) k =
        (jet gs rs).eval (2^(width+1)) := by
    rw [eval_jet_int]
    simp [prefixMoment, rs, List.map_map, Function.comp_def]
  change masked width digits
    (prefixMoment (2^(width+1) : ℤ) (gs.map fun g => (g.rate,g.weight (2^(width+1)))) k) =
      true at hm
  rw [he] at hm
  refine DimThree.PackedCheck.eval₂_nonneg_of_polynomial_mask (jet gs rs)
    (n := digits) (w := width) hdegree ?_ (by simpa [masked] using hm) x hx
  intro j
  have ha := (hc j).trans_lt hsmall
  exact ⟨(abs_lt.mp ha).1.le, (abs_lt.mp ha).2⟩

end RefinedBMV.ZeroSpectrum
