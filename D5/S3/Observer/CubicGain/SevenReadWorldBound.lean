/- GID: D5/S3/Observer/CubicGain/SevenReadWorldBound
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/SevenReadWorldBound
   mirror-E: none(waiver:seven-read-complete-world-fiber)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: Root multiplicity bounds complete original seven-reading worlds at each positive source width. -/

import D5.S3.Observer.CubicGain.FullWorldMeanSpan
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card

/-! Literal seven-row fibers with source multiplicity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace D5.S3.Observer.CubicGain.SevenReadWorldBound
open D5.S3.Observer.CubicGain Polynomial

/-- False selects J and true selects M at the sixth action. -/
def sevenProduct (e : Bool) (i : ℕ) : Mat :=
  ([actionJ,actionM,actionJ,actionM,actionJ,
    if e then actionM else actionJ].take i).foldl (fun Q E => E*Q) 1

/-- Original clocks and one fixed complete world in every row. -/
def sevenRead (e : Bool) (W : OriginalWorld) (i : ℕ) : ℝ :=
  W.2.2.1 + (originalPolynomial W).eval (i : ℝ) *
    Matrix.trace (sevenProduct e i * sourceMatrix W.1 W.2.1)

/-- The entire literal fiber at one specified positive width. -/
def sevenFiber (e : Bool) (b A C z Y p v : ℝ) : Set OriginalWorld :=
  {W | FullWorldMeanSpan.FullWorld W ∧ W.2.1=b ∧
    ∀ i : Fin 7, sevenRead e W i = (![0,A,C,z,Y,p,v] : Fin 7 → ℝ) i}

def sixthIndex (e : Bool) : ℝ := if e then 3 else 2

def interpolationDenominator (e : Bool) (b : ℝ) : ℝ :=
  16*(1+b)*(1+2*b)*(1+sixthIndex e*b)

/-- Even interpolation numerators, as polynomials in the drift. -/
def evenNumerators (e : Bool) (b C Y v : ℝ) : Fin 4 → Polynomial ℝ :=
  let T := 1+b
  let U := 1+2*b
  let V := 1+sixthIndex e*b
  ![-X*Polynomial.C (T*U*V), (Polynomial.C C-X)*Polynomial.C (U*V),
    (Polynomial.C Y-X)*Polynomial.C (T*V), (Polynomial.C v-X)*Polynomial.C (T*U)]

def oddNumerators (e : Bool) (b C Y v : ℝ) : Fin 3 → Polynomial ℝ :=
  let B := evenNumerators e b C Y v
  ![5*B 0+15*B 1-5*B 2+B 3,
    -B 0+9*B 1+9*B 2-B 3, B 0-5*B 1+15*B 2+5*B 3]

/-- The native elimination polynomial retains odd sampled zeros. -/
def driftPolynomial (e : Bool) (b A C z Y p v : ℝ) : Polynomial ℝ :=
  let G := oddNumerators e b C Y v
  (Polynomial.C A-X)*G 1*G 2-2*(Polynomial.C z-X)*G 0*G 2+
    (Polynomial.C p-X)*G 0*G 1

private theorem seven_traces (e : Bool) (r b : ℝ) :
    (fun i : Fin 7 => Matrix.trace (sevenProduct e i * sourceMatrix r b)) =
      ![1,sourceJ r b,1+b,sourceJ r b+r,1+2*b,
        sourceJ r b+2*r,1+sixthIndex e*b] := by
  cases e <;> ext i <;> fin_cases i <;>
    norm_num [sevenProduct,sourceMatrix,actionJ,actionM,Matrix.mul_apply,
      Matrix.trace,Fin.sum_univ_two,sourceJ,sixthIndex]
  all_goals ring

private theorem fiber_equations {e : Bool} {b A C z Y p v : ℝ}
    {W : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v) :
    ∀ i : Fin 7, W.2.2.1+(originalPolynomial W).eval (i : ℝ)*
      (![1,sourceJ W.1 b,1+b,sourceJ W.1 b+W.1,1+2*b,
        sourceJ W.1 b+2*W.1,1+sixthIndex e*b] : Fin 7 → ℝ) i =
      (![0,A,C,z,Y,p,v] : Fin 7 → ℝ) i := by
  intro i
  have h := hW.2.2 i
  unfold sevenRead at h
  rw [hW.2.1,congrFun (seven_traces e W.1 b) i] at h
  exact h

private theorem even_interpolation (a : Gain) :
    ∀ i : Fin 3, 16*(Polynomial.ofFn 4 a).eval (2*(i : ℝ)+1) =
      (![5, -1, 1] : Fin 3 → ℝ) i*(Polynomial.ofFn 4 a).eval 0+
      (![15,9,-5] : Fin 3 → ℝ) i*(Polynomial.ofFn 4 a).eval 2+
      (![-5,9,15] : Fin 3 → ℝ) i*(Polynomial.ofFn 4 a).eval 4+
      (![1,-1,5] : Fin 3 → ℝ) i*(Polynomial.ofFn 4 a).eval 6 := by
  intro i
  fin_cases i <;>
    norm_num [Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four]
  all_goals ring

private theorem denominator_pos (e : Bool) {b : ℝ} (hb : 0 < b) :
    0 < interpolationDenominator e b := by
  cases e <;> dsimp [interpolationDenominator,sixthIndex] <;> positivity

private theorem scaled_odd {e : Bool} {b A C z Y p v : ℝ}
    {W : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v) :
    ∀ i : Fin 3, interpolationDenominator e b*
      (originalPolynomial W).eval (2*(i : ℝ)+1) =
        (oddNumerators e b C Y v i).eval W.2.2.1 := by
  have h0 := fiber_equations hW 0
  have h2 := fiber_equations hW 2
  have h4 := fiber_equations hW 4
  have h6 := fiber_equations hW 6
  norm_num at h0 h2 h4 h6
  intro i
  have h := even_interpolation W.2.2.2 i
  change 16*(originalPolynomial W).eval _ = _ at h
  simp only [originalPolynomial] at h0 h2 h4 h6 h ⊢
  fin_cases i <;> norm_num [oddNumerators,evenNumerators] at h ⊢
  · dsimp [interpolationDenominator]
    linear_combination (1+b)*(1+2*b)*(1+sixthIndex e*b)*h +
      5*(1+b)*(1+2*b)*(1+sixthIndex e*b)*h0 +
      15*(1+2*b)*(1+sixthIndex e*b)*h2 -
      5*(1+b)*(1+sixthIndex e*b)*h4 + (1+b)*(1+2*b)*h6
  · dsimp [interpolationDenominator]
    linear_combination (1+b)*(1+2*b)*(1+sixthIndex e*b)*h -
      (1+b)*(1+2*b)*(1+sixthIndex e*b)*h0 +
      9*(1+2*b)*(1+sixthIndex e*b)*h2 +
      9*(1+b)*(1+sixthIndex e*b)*h4 - (1+b)*(1+2*b)*h6
  · dsimp [interpolationDenominator]
    linear_combination (1+b)*(1+2*b)*(1+sixthIndex e*b)*h +
      (1+b)*(1+2*b)*(1+sixthIndex e*b)*h0 -
      5*(1+2*b)*(1+sixthIndex e*b)*h2 +
      15*(1+b)*(1+sixthIndex e*b)*h4 + 5*(1+b)*(1+2*b)*h6

private theorem odd_equations {e : Bool} {b A C z Y p v : ℝ}
    {W : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v) :
    ∀ i : Fin 3, (oddNumerators e b C Y v i).eval W.2.2.1 *
      (sourceJ W.1 b+(i : ℝ)*W.1) =
        interpolationDenominator e b*((![A,z,p] : Fin 3 → ℝ) i-W.2.2.1) := by
  intro i
  rw [← scaled_odd hW i]
  fin_cases i
  · have h := fiber_equations hW 1
    norm_num at h ⊢
    linear_combination interpolationDenominator e b*h
  · have h := fiber_equations hW 3
    norm_num at h ⊢
    linear_combination interpolationDenominator e b*h
  · have h := fiber_equations hW 5
    norm_num at h ⊢
    linear_combination interpolationDenominator e b*h

private theorem native_root {e : Bool} {b A C z Y p v : ℝ} (hb : 0 < b)
    {W : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v) :
    (driftPolynomial e b A C z Y p v).eval W.2.2.1=0 := by
  have h0 := odd_equations hW 0
  have h1 := odd_equations hW 1
  have h2 := odd_equations hW 2
  norm_num at h0 h1 h2
  have hK := ne_of_gt (denominator_pos e hb)
  apply (mul_eq_zero.mp (show interpolationDenominator e b*
    (driftPolynomial e b A C z Y p v).eval W.2.2.1=0 from ?_)).resolve_left hK
  simp only [driftPolynomial,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_ofNat]
  linear_combination
    -(oddNumerators e b C Y v 1).eval W.2.2.1 *
      (oddNumerators e b C Y v 2).eval W.2.2.1*h0 +
    2*(oddNumerators e b C Y v 0).eval W.2.2.1 *
      (oddNumerators e b C Y v 2).eval W.2.2.1*h1 -
    (oddNumerators e b C Y v 0).eval W.2.2.1 *
      (oddNumerators e b C Y v 1).eval W.2.2.1*h2

private theorem drift_degree (e : Bool) (b A C z Y p v : ℝ) :
    (driftPolynomial e b A C z Y p v).degree ≤ 3 := by
  unfold driftPolynomial oddNumerators evenNumerators
  dsimp
  compute_degree

private theorem drift_coefficient (e : Bool) (b A C z Y p v : ℝ) :
    (driftPolynomial e b A C z Y p v).coeff 3 =
      if e then 192*b^4*(3*b^2+12*b+4)
      else 16*b*(1+2*b)^2*(4*b^3+16*b^2+5*b+8) := by
  cases e <;> dsimp [driftPolynomial,oddNumerators,evenNumerators,sixthIndex]
  all_goals compute_degree <;> norm_num <;> ring

private theorem drift_nonzero (e : Bool) {b : ℝ} (hb : 0 < b)
    (A C z Y p v : ℝ) : driftPolynomial e b A C z Y p v ≠ 0 := by
  intro h
  have hc := drift_coefficient e b A C z Y p v
  rw [h] at hc
  have hp : 0 < (if e then 192*b^4*(3*b^2+12*b+4)
      else 16*b*(1+2*b)^2*(4*b^3+16*b^2+5*b+8)) := by
    cases e <;> dsimp <;> positivity
  simp only [coeff_zero] at hc
  linarith

private theorem same_drift_gain {e : Bool} {b A C z Y p v : ℝ} (hb : 0 < b)
    {W V : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v)
    (hV : V ∈ sevenFiber e b A C z Y p v) (hd : W.2.2.1=V.2.2.1) :
    originalPolynomial W=originalPolynomial V := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := Finset.univ) (v := fun i : Fin 4 => 2*(i : ℝ))
  · intro i _ j _ hij
    apply Fin.ext
    have hh : (i : ℝ)=(j : ℝ) := mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hij
    exact_mod_cast hh
  · simpa [originalPolynomial] using Polynomial.ofFn_degree_lt W.2.2.2
  · simpa [originalPolynomial] using Polynomial.ofFn_degree_lt V.2.2.2
  · intro i _
    have w0 := fiber_equations hW 0
    have w2 := fiber_equations hW 2
    have w4 := fiber_equations hW 4
    have w6 := fiber_equations hW 6
    have v0 := fiber_equations hV 0
    have v2 := fiber_equations hV 2
    have v4 := fiber_equations hV 4
    have v6 := fiber_equations hV 6
    rw [hd] at w0 w2 w4 w6
    norm_num at w0 w2 w4 w6 v0 v2 v4 v6
    fin_cases i <;> norm_num
    · linarith
    · apply mul_right_cancel₀ (by positivity : (1+b : ℝ) ≠ 0)
      linarith
    · apply mul_right_cancel₀ (by positivity : (1+2*b : ℝ) ≠ 0)
      linarith
    · have hpos : 0 < 1+sixthIndex e*b := by
        cases e <;> dsimp [sixthIndex] <;> positivity
      apply mul_right_cancel₀ (ne_of_gt hpos)
      linarith

private theorem same_drift_r_world {e : Bool} {b A C z Y p v : ℝ} (hb : 0 < b)
    {W V : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v)
    (hV : V ∈ sevenFiber e b A C z Y p v)
    (hd : W.2.2.1=V.2.2.1) (hr : W.1=V.1) : W=V := by
  apply Prod.ext hr
  apply Prod.ext (hW.2.1.trans hV.2.1.symm)
  apply Prod.ext hd
  exact Polynomial.injective_ofFn 4 (same_drift_gain hb hW hV hd)

private theorem early_active {e : Bool} {b A C z Y p v : ℝ} (hb : 0 < b)
    (hz : z ≠ A) {W : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v) :
    (oddNumerators e b C Y v 0).eval W.2.2.1 ≠ 0 ∨
    (oddNumerators e b C Y v 1).eval W.2.2.1 ≠ 0 := by
  by_cases h0 : (oddNumerators e b C Y v 0).eval W.2.2.1=0
  · right
    intro h1
    have w0 := odd_equations hW 0
    have w1 := odd_equations hW 1
    rw [h0] at w0
    rw [h1] at w1
    norm_num at w0 w1
    have ha := w0.resolve_left (ne_of_gt (denominator_pos e hb))
    have hz' := w1.resolve_left (ne_of_gt (denominator_pos e hb))
    exact hz (by linarith)
  · exact Or.inl h0

private theorem fixed_active_trace {e : Bool} {b A C z Y p v : ℝ}
    {W V : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v)
    (hV : V ∈ sevenFiber e b A C z Y p v) (hd : W.2.2.1=V.2.2.1)
    (i : Fin 3) (hi : (oddNumerators e b C Y v i).eval V.2.2.1 ≠ 0) :
    sourceJ W.1 b+(i : ℝ)*W.1=sourceJ V.1 b+(i : ℝ)*V.1 := by
  have w := odd_equations hW i
  have v := odd_equations hV i
  rw [hd] at w
  exact mul_left_cancel₀ hi (w.trans v.symm)

private theorem two_active_equal {e : Bool} {b A C z Y p v : ℝ} (hb : 0 < b)
    {W V : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v)
    (hV : V ∈ sevenFiber e b A C z Y p v) (hd : W.2.2.1=V.2.2.1)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : (oddNumerators e b C Y v i).eval V.2.2.1 ≠ 0)
    (hj : (oddNumerators e b C Y v j).eval V.2.2.1 ≠ 0) : W=V := by
  have hti := fixed_active_trace hW hV hd i hi
  have htj := fixed_active_trace hW hV hd j hj
  have hn : (i : ℝ)-(j : ℝ) ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast (sub_eq_zero.mp h)
  have he : ((i : ℝ)-(j : ℝ))*(W.1-V.1)=0 := by
    linear_combination hti-htj
  exact same_drift_r_world hb hW hV hd
    (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn))

private theorem source_relation {b : ℝ} (hb : b ≠ 0) (r : ℝ) :
    b*(sourceJ r b-b)=r*(1-r) := by
  dsimp [sourceJ]
  field_simp
  <;> ring

private theorem same_drift_card_le_two {e : Bool} {b A C z Y p v d : ℝ}
    (hb : 0 < b) (hz : z ≠ A) (S : Finset OriginalWorld)
    (hS : ∀ W ∈ S, W ∈ sevenFiber e b A C z Y p v ∧ W.2.2.1=d) :
    S.card ≤ 2 := by
  classical
  by_cases he : S.Nonempty
  · obtain ⟨V,hV⟩ := he
    obtain ⟨hv,hvd⟩ := hS V hV
    have hactive := early_active hb hz hv
    obtain ⟨i,hi⟩ : ∃ i : Fin 3, (i=0 ∨ i=1) ∧
        (oddNumerators e b C Y v i).eval V.2.2.1 ≠ 0 := by
      rcases hactive with h | h
      · exact ⟨0,Or.inl rfl,h⟩
      · exact ⟨1,Or.inr rfl,h⟩
    have hinj : Set.InjOn (fun W : OriginalWorld => W.1) S := by
      intro W hw U hu hru
      exact same_drift_r_world hb (hS W hw).1 (hS U hu).1
        ((hS W hw).2.trans (hS U hu).2.symm) hru
    rw [← Finset.card_image_iff.mpr hinj]
    apply le_trans (Finset.card_le_card (t := {V.1,1+(i : ℝ)*b-V.1}) ?_)
      (by by_cases h : V.1=1+(i : ℝ)*b-V.1 <;> simp [h])
    intro r hr
    obtain ⟨W,hw,rfl⟩ := Finset.mem_image.mp hr
    have htrace := fixed_active_trace (hS W hw).1 hv ((hS W hw).2.trans hvd.symm) i hi.2
    have hfactor : (W.1-V.1)*(W.1+V.1-1-(i : ℝ)*b)=0 := by
      linear_combination -b*htrace + source_relation (ne_of_gt hb) W.1 -
        source_relation (ne_of_gt hb) V.1
    rcases mul_eq_zero.mp hfactor with h | h
    · simp [sub_eq_zero.mp h]
    · have hh : W.1=1+(i : ℝ)*b-V.1 := by linarith
      simp [hh]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    omega

private theorem square_dvd_three {q a b c : Polynomial ℝ}
    (ha : q ∣ a) (hb : q ∣ b) : q^2 ∣ a*c*b := by
  simpa [pow_two,mul_assoc,mul_left_comm,mul_comm] using
    dvd_mul_of_dvd_left (mul_dvd_mul ha hb) c

private theorem distinct_same_drift_double {e : Bool} {b A C z Y p v : ℝ}
    (hb : 0 < b) (hz : z ≠ A)
    {W V : OriginalWorld} (hW : W ∈ sevenFiber e b A C z Y p v)
    (hV : V ∈ sevenFiber e b A C z Y p v)
    (hd : W.2.2.1=V.2.2.1) (hne : W ≠ V) :
    (X-Polynomial.C V.2.2.1)^2 ∣ driftPolynomial e b A C z Y p v := by
  have hearly := early_active hb hz hV
  have h5 : (oddNumerators e b C Y v 2).eval V.2.2.1=0 := by
    by_contra h
    rcases hearly with ha | ha
    · exact hne (two_active_equal hb hW hV hd 0 2 (by decide) ha h)
    · exact hne (two_active_equal hb hW hV hd 1 2 (by decide) ha h)
  have h01 : (oddNumerators e b C Y v 0).eval V.2.2.1=0 ∨
      (oddNumerators e b C Y v 1).eval V.2.2.1=0 := by
    by_cases h0 : (oddNumerators e b C Y v 0).eval V.2.2.1=0
    · exact Or.inl h0
    · right
      by_contra h1
      exact hne (two_active_equal hb hW hV hd 0 1 (by decide) h0 h1)
  have hK := ne_of_gt (denominator_pos e hb)
  have hp : p=V.2.2.1 := by
    have h := odd_equations hV 2
    rw [h5] at h
    simpa [hK,sub_eq_zero] using h.symm
  have hG5 : X-Polynomial.C V.2.2.1 ∣ oddNumerators e b C Y v 2 :=
    Polynomial.dvd_iff_isRoot.mpr h5
  have hP : X-Polynomial.C V.2.2.1 ∣ Polynomial.C p-X := by
    apply Polynomial.dvd_iff_isRoot.mpr
    simp [Polynomial.IsRoot,hp]
  unfold driftPolynomial
  dsimp
  rcases h01 with h0 | h1
  · have ha : A=V.2.2.1 := by
      have h := odd_equations hV 0
      rw [h0] at h
      simpa [hK,sub_eq_zero] using h.symm
    have hA : X-Polynomial.C V.2.2.1 ∣ Polynomial.C A-X := by
      apply Polynomial.dvd_iff_isRoot.mpr
      simp [Polynomial.IsRoot,ha]
    have hG0 : X-Polynomial.C V.2.2.1 ∣ oddNumerators e b C Y v 0 :=
      Polynomial.dvd_iff_isRoot.mpr h0
    apply dvd_add
    · apply dvd_sub
      · exact square_dvd_three hA hG5
      · simpa [mul_assoc,mul_left_comm,mul_comm] using
          (square_dvd_three (c := 2*(Polynomial.C z-X)) hG0 hG5)
    · exact square_dvd_three hP hG0
  · have hz' : z=V.2.2.1 := by
      have h := odd_equations hV 1
      rw [h1] at h
      simpa [hK,sub_eq_zero] using h.symm
    have hZ : X-Polynomial.C V.2.2.1 ∣ Polynomial.C z-X := by
      apply Polynomial.dvd_iff_isRoot.mpr
      simp [Polynomial.IsRoot,hz']
    have hG1 : X-Polynomial.C V.2.2.1 ∣ oddNumerators e b C Y v 1 :=
      Polynomial.dvd_iff_isRoot.mpr h1
    apply dvd_add
    · apply dvd_sub
      · simpa [mul_assoc,mul_left_comm,mul_comm] using
          (square_dvd_three (c := Polynomial.C A-X) hG1 hG5)
      · simpa [mul_assoc,mul_left_comm,mul_comm] using
          (square_dvd_three (c := 2*oddNumerators e b C Y v 0) hZ hG5)
    · exact square_dvd_three hP hG1

/-- Distinct complete worlds consume drift roots with their full multiplicity. -/
theorem native_drift_multiset_le_roots (e : Bool) (b A C z Y p v : ℝ)
    (hb : 0 < b) (hz : z ≠ A) (S : Finset OriginalWorld)
    (hS : ∀ W ∈ S, W ∈ sevenFiber e b A C z Y p v) :
    S.val.map (fun W => W.2.2.1) ≤ (driftPolynomial e b A C z Y p v).roots := by
  classical
  apply Multiset.le_iff_count.mpr
  intro d
  rw [Multiset.count_map,Polynomial.count_roots]
  let T := S.filter (fun W => d=W.2.2.1)
  change T.card ≤ Polynomial.rootMultiplicity d (driftPolynomial e b A C z Y p v)
  have hT : ∀ W ∈ T, W ∈ sevenFiber e b A C z Y p v ∧ W.2.2.1=d := by
    intro W hw
    obtain ⟨hs,hd⟩ := Finset.mem_filter.mp hw
    exact ⟨hS W hs,hd.symm⟩
  by_cases he : T.Nonempty
  · have hbound := same_drift_card_le_two hb hz T hT
    have hnonzero := drift_nonzero e hb A C z Y p v
    by_cases hc : T.card ≤ 1
    · obtain ⟨W,hw⟩ := he
      have hroot := native_root hb (hT W hw).1
      rw [(hT W hw).2] at hroot
      have hone : 1 ≤ Polynomial.rootMultiplicity d (driftPolynomial e b A C z Y p v) := by
        rw [Polynomial.le_rootMultiplicity_iff hnonzero,pow_one,Polynomial.dvd_iff_isRoot]
        exact hroot
      exact hc.trans hone
    · obtain ⟨W,hw,V,hv,hne⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
      have hd := (hT W hw).2.trans (hT V hv).2.symm
      have hdiv := distinct_same_drift_double hb hz (hT W hw).1 (hT V hv).1 hd hne
      rw [(hT V hv).2] at hdiv
      exact hbound.trans ((Polynomial.le_rootMultiplicity_iff hnonzero).mpr hdiv)
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

end D5.S3.Observer.CubicGain.SevenReadWorldBound
