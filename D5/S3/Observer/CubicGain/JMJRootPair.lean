/- GID: D5/S3/Observer/CubicGain/JMJRootPair
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/JMJRootPair
   mirror-E: none(waiver:native-jmj-quadratic-root-worlds)
   anchors: [mathlib/module/Mathlib.Algebra.QuadraticDiscriminant]
   utility: none
   digest: The two canonical quadratic roots give legal complete worlds with the actual JMJJ history and three-step failure. -/
import D5.S3.Observer.CubicGain.JMJPairLosing
import Mathlib.Algebra.QuadraticDiscriminant
/-! Legal quadratic-root pairs at the actual fourth J child of JMJ. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.CubicGain.JMJRootPair
open D5.S3.Observer.Linear.GainRay
open D5.S3.Observer.CubicGain.MixedTripleExclusion
open D5.S3.Observer.CubicGain.JMJPairLosing

def q (a B : ℝ) : ℝ := B^2 - (a+4/5)*B + 6/5*a-a^2
def discriminant (a : ℝ) : ℝ := 5*a^2-16/5*a+16/25
def lowerRoot (a : ℝ) : ℝ := (a+4/5-Real.sqrt (discriminant a))/2
def upperRoot (a : ℝ) : ℝ := (a+4/5+Real.sqrt (discriminant a))/2
def rootMatrix (a B : ℝ) : Mat := !![a,B;4/5-B,6/5-a-B]
def rootScale (B : ℝ) : ℝ := 6/5-B

def RootData (a B : ℝ) : Prop := 0 < B ∧ B < 4/5 ∧ q a B = 0

private theorem root_bounds (a : ℝ) (ha : 0 < a ∧ a < 2/5) :
    RootData a (lowerRoot a) ∧ RootData a (upperRoot a) ∧ lowerRoot a < upperRoot a := by
  have hd : 0 < discriminant a := by
    dsimp [discriminant]
    nlinarith [sq_nonneg (a-8/25)]
  have hs := Real.sq_sqrt hd.le
  have hp := Real.sqrt_pos.2 hd
  have hs0 := Real.sqrt_nonneg (discriminant a)
  have hprod : 0 < a*(6/5-a) := mul_pos ha.1 (by linarith [ha.2])
  have hend : 0 < a*(2/5-a) := mul_pos ha.1 (by linarith [ha.2])
  have hl : Real.sqrt (discriminant a) < a+4/5 := by
    apply (Real.sqrt_lt' (by linarith [ha.1] : 0 < a+4/5)).2
    dsimp [discriminant]
    nlinarith
  have hu : Real.sqrt (discriminant a) < 4/5-a := by
    apply (Real.sqrt_lt' (by linarith [ha.2] : 0 < 4/5-a)).2
    dsimp [discriminant]
    nlinarith
  have hr (B : ℝ) : q a B = 0 ↔ B = upperRoot a ∨ B = lowerRoot a := by
    have hh := quadratic_eq_zero_iff (a := (1:ℝ)) (b := -(a+4/5))
      (c := 6/5*a-a^2) (by norm_num)
      (s := Real.sqrt (discriminant a)) (by
        dsimp [discrim, discriminant] at *
        nlinarith [hs]) B
    convert hh using 2 <;> dsimp [q,upperRoot,lowerRoot] <;> ring
  refine ⟨⟨?_,?_,(hr _).2 (Or.inr rfl)⟩,⟨?_,?_,(hr _).2 (Or.inl rfl)⟩,?_⟩
  all_goals dsimp [lowerRoot,upperRoot]; linarith

private theorem root_legal (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) :
    LegalSource ((rootScale B)⁻¹ • rootMatrix a B) := by
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have hs : 0 < rootScale B := by dsimp [rootScale]; linarith [hB.2.1]
  have hc : 0 < 4/5-B := by linarith [hB.2.1]
  have hq := hB.2.2
  dsimp [q] at hq
  have hden : 1 + ((4/5-B)/a)*(B/a) = rootScale B / a := by
    field_simp
    dsimp [rootScale]
    nlinarith
  have he : (rootScale B)⁻¹ • rootMatrix a B = sourceChart ((4/5-B)/a) (B/a) := by
    rw [sourceChart,hden]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rootMatrix,Matrix.smul_apply,smul_eq_mul]
    all_goals field_simp
    all_goals dsimp [rootScale] at *; nlinarith
  rw [he]
  exact source_chart_legal _ _ (div_pos hc ha.1) (div_pos hB.1 ha.1)

/-- The whole coefficient vector is s times the coefficients of t(t-6)(t-7). -/
def rootWorld (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) : World3 where
  source := (rootScale B)⁻¹ • rootMatrix a B
  legal := root_legal a B ha hB
  coeff := ![0,42*rootScale B,-13*rootScale B,rootScale B]
  nonzero := by
    intro h
    have hh := congrFun h 3
    have hs : 0 < rootScale B := by dsimp [rootScale]; linarith [hB.2.1]
    norm_num at hh
    linarith
  drift := 0

def lowerWorld (a : ℝ) (ha : 0 < a ∧ a < 2/5) : World3 :=
  rootWorld a (lowerRoot a) ha (root_bounds a ha).1

def upperWorld (a : ℝ) (ha : 0 < a ∧ a < 2/5) : World3 :=
  rootWorld a (upperRoot a) ha (root_bounds a ha).2.1

private theorem root_gain (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) (t : ℝ) :
    (gain 3 (rootWorld a B ha hB).coeff).eval t = rootScale B * (t*(t-6)*(t-7)) := by
  norm_num [gain,rootWorld,Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_succ]
  ring

private theorem root_read (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B)
    (u : List Bool) (i : ℕ) :
    readAt (rootWorld a B ha hB) u i =
      ((i:ℝ)*((i:ℝ)-6)*((i:ℝ)-7))*Matrix.trace (acquisition (u.take i)*rootMatrix a B) := by
  have hs : rootScale B ≠ 0 := ne_of_gt (by dsimp [rootScale]; linarith [hB.2.1])
  rw [readAt,root_gain]
  simp only [rootWorld, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, add_zero]
  field_simp

private theorem root_history (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) :
    readings (rootWorld a B ha hB) [true,false,true,true] =
      ![0,24,48,36*(a+4/5),144/5] := by
  ext i
  change readAt (rootWorld a B ha hB) [true,false,true,true] i = _
  rw [root_read]
  fin_cases i <;>
    norm_num [acquisition,Raw,rootMatrix,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two] <;> ring

private theorem root_fifth (a B : ℝ) (ha : 0 < a ∧ a < 2/5) (hB : RootData a B) (F : Bool) :
    readAt (rootWorld a B ha hB) [true,false,true,true,F] 5 =
      if F then 10*(a+4/5) else 20 := by
  rw [root_read]
  cases F <;>
    norm_num [acquisition,Raw,rootMatrix,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two] <;> ring

/-- Both quadratic-root worlds are legal native worlds, realize the same actual
JMJJ child, remain distinct, and lose for three further original-clock actions. -/
theorem canonical_pair_losing (a : ℝ) (ha : 0 < a ∧ a < 2/5) :
    lowerWorld a ha ≠ upperWorld a ha ∧
    readings (lowerWorld a ha) [true,false,true,true] = ![0,24,48,36*(a+4/5),144/5] ∧
    readings (upperWorld a ha) [true,false,true,true] = ![0,24,48,36*(a+4/5),144/5] ∧
    Losing 3 {lowerWorld a ha,upperWorld a ha} [true,false,true,true] := by
  have hne : lowerWorld a ha ≠ upperWorld a ha := by
    intro h
    have hh := congrArg (fun W : World3 => W.coeff 3) h
    change rootScale (lowerRoot a) = rootScale (upperRoot a) at hh
    have hl := (root_bounds a ha).2.2
    dsimp [rootScale] at hh
    linarith
  have hl := root_history a (lowerRoot a) ha (root_bounds a ha).1
  have hu := root_history a (upperRoot a) ha (root_bounds a ha).2.1
  refine ⟨hne,hl,hu,?_⟩
  apply (jmj_pair_losing_iff 3 (by omega) true (36*(a+4/5)) (144/5) _ _ hne hl hu).2
  refine ⟨rfl,?_,?_⟩
  · intro j hj hjn
    interval_cases j <;> simp [lowerWorld,upperWorld,root_gain]
  · intro F
    simp only [lowerWorld,upperWorld,root_fifth]

end D5.S3.Observer.CubicGain.JMJRootPair
