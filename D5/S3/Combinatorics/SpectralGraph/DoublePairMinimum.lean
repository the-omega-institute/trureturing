/- GID: D5/S3/Combinatorics/SpectralGraph/DoublePairMinimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/DoublePairMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine full-operator minimum intervals at every double-pair threshold. -/
import D5.S3.Combinatorics.SpectralGraph.DoublePairSpectrum
import D5.S3.Combinatorics.SpectralGraph.PairedTensorMinimum

/-! Source: complete four-prime-double-pair-completion, PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. The three threshold regions
refer to the smallest eigenvalue of the full four-cell operator, compared
with every nonzero eigenpair, not just a selected cubic root. The eight
fixed brackets and the unbounded threshold are reused from DoublePairCubic.
All positive double pairs include the diagonal and the a=1 boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000
noncomputable section
open Matrix Finset
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.DoublePairMinimum
open PairedIdealIntersectionObstructions DoublePairCubic

private theorem cubic_comparison (A B C D x y : ℝ) :
    x^3*(A*y^3-B*y^2-C*y-D)-y^3*(A*x^3-B*x^2-C*x-D)=
      (y-x)*(B*x^2*y^2+C*x*y*(x+y)+D*(x^2+x*y+y^2)) := by ring

private theorem cubic_negative (A B C D x l : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : 0 < x) (hl : x ≤ l)
    (hf : A*l^3-B*l^2-C*l-D < 0) : A*x^3-B*x^2-C*x-D < 0 := by
  have hc := cubic_comparison A B C D x l
  have hln : 0 < l := by linarith
  have hn : 0 ≤ (l-x)*(B*x^2*l^2+C*x*l*(x+l)+D*(x^2+x*l+l^2)) := by
    have hdiff : 0 ≤ l-x := by linarith
    positivity
  have hneg := mul_neg_of_pos_of_neg (pow_pos hx 3) hf
  have hp : 0 < l^3 := pow_pos hln 3
  nlinarith

private theorem cubic_positive (A B C D x u : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hu : 0 < u) (hx : u ≤ x)
    (hf : 0 < A*u^3-B*u^2-C*u-D) : 0 < A*x^3-B*x^2-C*x-D := by
  have hc := cubic_comparison A B C D u x
  have hxn : 0 < x := by linarith
  have hn : 0 ≤ (x-u)*(B*u^2*x^2+C*u*x*(u+x)+D*(u^2+u*x+x^2)) := by
    have hdiff : 0 ≤ x-u := by linarith
    positivity
  have hpos := mul_pos (pow_pos hxn 3) hf
  have hp : 0 < u^3 := pow_pos hu 3
  nlinarith

/-- Complete strict sign information on both sides of the endpoint-two
exponent gap. There is no upper bound on a or b. -/
theorem two_signs (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b) :
    (b ≤ 2*a^2-2 → P2 a b < 0) ∧ (2*a^2-1 ≤ b → 0 < P2 a b) := by
  have hB : 0 ≤ (a-1)*(4*a^2+6*a+1) := mul_nonneg (by linarith) (by positivity)
  have hC : 0 ≤ (a-1)*(4*a^2-3) := mul_nonneg (by linarith) (by nlinarith)
  have hD : 0 ≤ (a-1)^2*(2*a-1) := mul_nonneg (sq_nonneg _) (by linarith)
  obtain ⟨hl,hu⟩ := two_bracket a ha
  constructor
  · intro h
    exact cubic_negative (2*a+1) _ _ _ b (2*a^2-2) hB hC hD hb h hl
  · intro h
    exact cubic_positive (2*a+1) _ _ _ b (2*a^2-1) hB hC hD (by nlinarith) h hu

/-- Complete strict endpoint-three signs, including the eight fixed
thresholds and every a>=13, together with the entire a=2,3,4 domain. -/
theorem three_signs (a b : ℕ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (5 ≤ a → (b ≤ DoublePairCubic.H a → P3 (a : ℝ) b < 0) ∧
      (DoublePairCubic.H a+1 ≤ b → 0 < P3 (a : ℝ) b)) ∧
    (a ≤ 4 → 0 < P3 (a : ℝ) b) := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hb
  have hpositive (ha3 : 3 ≤ a) :
      0 ≤ (a : ℝ)*((a : ℝ)-2)*(4*(a : ℝ)+5) ∧
      0 ≤ 2*((a : ℝ)-2)*(2*(a : ℝ)^2-2*(a : ℝ)-3) ∧
      0 ≤ 2*((a : ℝ)-2)^2*((a : ℝ)-1) := by
    have ha3R : (3 : ℝ) ≤ a := by exact_mod_cast ha3
    refine ⟨mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity),
      mul_nonneg (by positivity) (by nlinarith),mul_nonneg (by positivity) (by linarith)⟩
  constructor
  · intro ha5
    obtain ⟨hB,hC,hD⟩ := hpositive (by omega)
    obtain ⟨hl,hu⟩ := three_bracket a ha5
    have hH : (0 : ℝ) < DoublePairCubic.H a := by
      have hh : 0 < DoublePairCubic.H a := by unfold DoublePairCubic.H; split_ifs <;> omega
      exact_mod_cast hh
    constructor
    · intro h
      exact cubic_negative (((a : ℝ)+2)*(2*(a : ℝ)+1)) _ _ _ b (DoublePairCubic.H a)
        hB hC hD hbR (by exact_mod_cast h) hl
    · intro h
      exact cubic_positive (((a : ℝ)+2)*(2*(a : ℝ)+1)) _ _ _ b ((DoublePairCubic.H a : ℝ)+1)
        hB hC hD (by linarith) (by exact_mod_cast h) hu
  · intro ha4
    by_cases ha2 : a=2
    · subst a
      dsimp [P3]
      norm_num
      positivity
    obtain ⟨hB,hC,hD⟩ := hpositive (by omega)
    have hsmall : a=3 ∨ a=4 := by omega
    have hpos : 0 < P3 (a : ℝ) (a : ℝ) := by
      rcases hsmall with rfl | rfl <;> norm_num [P3]
    exact cubic_positive (((a : ℝ)+2)*(2*(a : ℝ)+1)) _ _ _ b a
      hB hC hD (by linarith) habR hpos

/-- The complete quadratic energy identity of the full double-pair
operator. Multiplication by positive denominators retains every square. -/
theorem shifted_energy (a b r : ℝ) (hb : 0 ≤ b) (v : Fin 2 × Fin 2 → ℝ) :
    let A := (2*a+1)*b+a+1-r
    let B := a+b+1-r
    let C := a+1-r
    let x := v (0,0)
    let y := v (0,1)
    let z := v (1,0)
    let w := v (1,1)
    2*A*C*(dotProduct v ((symmetricK a b b-r • 1)*ᵥv)) =
      C*(A*(y+z)+2*a*Real.sqrt b*x)^2+A*C*B*(y-z)^2+
        2*A*(C*w+a*b*x)^2-2*p a b r*x^2 := by
  dsimp only
  simp [dotProduct,mulVec,Fintype.sum_prod_type,Fin.sum_univ_succ,symmetricK,E,PairedIdealIntersectionObstructions.H,
    Matrix.one_apply,kroneckerMap_apply,p,Q,Matrix.scalar,Matrix.det_fin_three]
  ring_nf
  simp only [Real.sq_sqrt hb]
  ring

/-- A negative cubic value strictly below a+1 places every full-operator
eigenvalue above r. This is an energy theorem, not a chosen-root premise. -/
theorem shift_posDef (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : r < a+1)
    (hp : p a b r < 0) : (symmetricK a b b-r • 1).PosDef := by
  let A := (2*a+1)*b+a+1-r
  let B := a+b+1-r
  let C := a+1-r
  have hA : 0 < A := by dsimp [A]; nlinarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (symmetric_hermitian a b b).sub (by simp)
  intro v hv
  have hi := shifted_energy a b r hb.le v
  change 2*A*C*_ = _ at hi
  have t0 : 0 ≤ C*(A*(v (0,1)+v (1,0))+2*a*Real.sqrt b*v (0,0))^2 := by positivity
  have t1 : 0 ≤ A*C*B*(v (0,1)-v (1,0))^2 := by positivity
  have t2 : 0 ≤ 2*A*(C*v (1,1)+a*b*v (0,0))^2 := by positivity
  have t3 : 0 ≤ -2*p a b r*(v (0,0))^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  by_contra! hn
  have hleft : 2*A*C*(dotProduct v ((symmetricK a b b-r • 1)*ᵥv)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
  have hx : v (0,0)=0 := by
    by_contra hx
    have ht : 0 < -2*p a b r*(v (0,0))^2 :=
      mul_pos (by linarith) (sq_pos_of_ne_zero hx)
    linarith only [hi,hleft,t0,t1,t2,ht]
  have hyz : v (0,1)+v (1,0)=0 := by
    by_contra hyz
    have hs : A*(v (0,1)+v (1,0))+2*a*Real.sqrt b*v (0,0) ≠ 0 := by
      rw [hx,mul_zero,add_zero]
      exact mul_ne_zero hA.ne' hyz
    have ht := mul_pos hC (sq_pos_of_ne_zero hs)
    linarith only [hi,hleft,t1,t2,t3,ht]
  have hyd : v (0,1)-v (1,0)=0 := by
    by_contra hyd
    have ht := mul_pos (mul_pos (mul_pos hA hC) hB) (sq_pos_of_ne_zero hyd)
    linarith only [hi,hleft,t0,t2,t3,ht]
  have hw : v (1,1)=0 := by
    by_contra hw
    have hs : C*v (1,1)+a*b*v (0,0) ≠ 0 := by
      rw [hx,mul_zero,add_zero]
      exact mul_ne_zero hC.ne' hw
    have ht := mul_pos (mul_pos (by norm_num : (0 : ℝ)<2) hA) (sq_pos_of_ne_zero hs)
    linarith only [hi,hleft,t0,t1,t3,ht]
  have hy : v (0,1)=0 := by linarith only [hyz,hyd]
  have hz : v (1,0)=0 := by linarith only [hyz,hyd]
  apply hv
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hw

private theorem eigenvalue_gt_of_posDef (a b r e : ℝ)
    (hp : (symmetricK a b b-r • 1).PosDef)
    (v : Fin 2 × Fin 2 → ℝ) (hv : v ≠ 0) (he : symmetricK a b b*ᵥv=e • v) : r < e := by
  have hpos := hp.dotProduct_mulVec_pos hv
  have hn : 0 < dotProduct v v := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hv
  have hshift : (symmetricK a b b-r • 1)*ᵥv=(e-r) • v := by
    rw [sub_mulVec,he,smul_mulVec,one_mulVec]
    ext q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hshift] at hpos
  simp only [star_trivial,dotProduct_smul,smul_eq_mul] at hpos
  nlinarith

/-- Cubic signs give a strict window for the genuine minimum, including
comparison with every real nonzero eigenpair of the full tensor. -/
theorem minimum_window (a b l u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : l=1 ∨ (l<a+1 ∧ p a b l<0))
    (hu : u<a+b+1) (hpu : 0 < p a b u) :
    ∃ e : ℝ, l < e ∧ e < u ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK a b b*ᵥh=e • h ∧
        ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z ≠ 0 → tensorK a b b*ᵥz=r • z → e ≤ r := by
  obtain ⟨e,he,h,hh,hE,hmin⟩ := PairedTensorMinimum.minimum a b b ha hb hb
  have hlow : l < e := by
    rcases hl with rfl | ⟨hl,hpl⟩
    · exact he
    have hd : (tensorK a b b-e • 1).det=0 := by
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨h,hh,?_⟩
      rw [sub_mulVec,hE,smul_mulVec,one_mulVec,sub_self]
    have hs : (symmetricK a b b-e • 1).det=0 := by
      rwa [tensor_symmetric_det_shift a b b e hb hb]
    obtain ⟨v,hv,hve⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
    have hSv : symmetricK a b b*ᵥv=e • v := by
      rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
      exact sub_eq_zero.mp hve
    exact eigenvalue_gt_of_posDef a b l e (shift_posDef a b l ha hb hl hpl) v hv hSv
  have hno : ¬(symmetricK a b b-u • 1).PosSemidef := by
    intro hp
    have hd := hp.det_nonneg
    rw [tensor_symmetric_det_shift a b b u hb hb,factorization] at hd
    have hn := mul_neg_of_neg_of_pos (sub_neg.mpr hu) hpu
    linarith
  obtain ⟨d,hd,v,hv,hSv⟩ := negative_eigenpair_of_not_posSemidef
    (symmetricK a b b-u • 1) ((symmetric_hermitian a b b).sub (by simp)) hno
  have hS : symmetricK a b b*ᵥv=(d+u) • v := by
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hSv
    ext q
    have ht := congrFun hSv q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  obtain ⟨z,hz,hze⟩ := tensor_eigenpair_of_symmetric a b b hb hb (d+u) v hv hS
  have hle := hmin (d+u) z hz hze
  exact ⟨e,hlow,by linarith,h,hh,hE,hmin⟩

/-- The entire lowest threshold region, with its equality boundary. -/
theorem low_region (a b : ℕ) (ha : 2 ≤ a) (hb : a ≤ b)
    (hcut : 2*a^2-1 ≤ b) :
    ∃ e : ℝ, 1 < e ∧ e < 2 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK (a : ℝ) b b*ᵥh=e • h ∧
        ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z ≠ 0 →
          tensorK (a : ℝ) b b*ᵥz=r • z → e ≤ r := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hcutR : 2*(a : ℝ)^2-1 ≤ b := by
    have hn : 2*a^2 ≤ b+1 := by omega
    have hr : 2*(a : ℝ)^2 ≤ (b : ℝ)+1 := by exact_mod_cast hn
    linarith
  apply minimum_window a b 1 2 (by linarith) hbR (Or.inl rfl) (by linarith)
  rw [endpoint_two]
  exact (two_signs a b haR hbR).2 hcutR

/-- The full middle region for a>=5, and the complete middle range at
smaller repeated exponents two through four. -/
theorem middle_region (a b : ℕ) (ha : 2 ≤ a) (hb : a ≤ b)
    (hlo : a ≤ 4 ∨ DoublePairCubic.H a+1 ≤ b) (hhi : b ≤ 2*a^2-2) :
    ∃ e : ℝ, 2 < e ∧ e < 3 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK (a : ℝ) b b*ᵥh=e • h ∧
        ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z ≠ 0 →
          tensorK (a : ℝ) b b*ᵥz=r • z → e ≤ r := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hhiR : (b : ℝ) ≤ 2*(a : ℝ)^2-2 := by
    have hn : b+2 ≤ 2*a^2 := by omega
    have hr : (b : ℝ)+2 ≤ 2*(a : ℝ)^2 := by exact_mod_cast hn
    linarith
  apply minimum_window a b 2 3 (by linarith) hbR
    (Or.inr ⟨by linarith,?_⟩) (by linarith) ?_
  · rw [endpoint_two]
    exact (two_signs a b haR hbR).1 hhiR
  · rw [endpoint_three]
    obtain ⟨hlarge,hsmall⟩ := three_signs a b ha hb
    rcases hlo with hs | hs
    · exact hsmall hs
    · by_cases ha5 : 5 ≤ a
      · exact (hlarge ha5).2 hs
      · exact hsmall (by omega)

/-- The full highest region, including b=a and b=H(a). -/
theorem high_region (a b : ℕ) (ha : 5 ≤ a) (hb : a ≤ b) (hcut : b ≤ DoublePairCubic.H a) :
    ∃ e : ℝ, 3 < e ∧ e < 4 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK (a : ℝ) b b*ᵥh=e • h ∧
        ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z ≠ 0 →
          tensorK (a : ℝ) b b*ᵥz=r • z → e ≤ r := by
  have haR : (5 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hb
  apply minimum_window a b 3 4 (by linarith) (by linarith)
    (Or.inr ⟨by linarith,?_⟩) (by linarith) (four_positive a b (by linarith) habR)
  rw [endpoint_three]
  exact ((three_signs a b (by omega) hb).1 ha).1 hcut

/-- The full a=1 boundary has its own smallest-root interval, with no
bound on the positive second exponent. -/
theorem unit_region (b : ℕ) (hb : 0 < b) :
    ∃ e : ℝ, 1 < e ∧ e < 2 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK 1 (b : ℝ) b*ᵥh=e • h ∧
        ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z ≠ 0 →
          tensorK 1 (b : ℝ) b*ᵥz=r • z → e ≤ r := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply minimum_window 1 b 1 2 (by norm_num) hbR (Or.inl rfl) (by linarith)
  rw [endpoint_two]
  norm_num [P2]
  positivity

end D5.S3.Combinatorics.SpectralGraph.DoublePairMinimum
