/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Balanced-star coefficients, complete-family coupling, and capped tail mass. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtBell
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Lattice
set_option autoImplicit false
open Matrix Finset
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
open UniformSchmidtIncidence UniformSchmidtSpectrum UniformSchmidtBell
noncomputable section

/-- Independent LABELLED assignments, with no numerical distinctness premise. -/
def family (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (π : Edge 5 ≃ Fin 10) (σ : BottomSlot 5 ≃ Fin 15) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  K (fun e => u+v+h (π e)) (fun b => u-d (σ b))
def FullPSD (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) : Prop :=
  ∀ (π : Edge 5 ≃ Fin 10) (σ : BottomSlot 5 ≃ Fin 15),
    (family u v h d π σ).PosSemidef

/-- All-ones test of the complete family. -/
theorem family_mass_budget (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (hf : FullPSD u v h d) : (∑ i,h i)+(∑ i,d i) ≤ 5*u-10*v := by
  have ha : a 5=10 := by
    have hc := edge_card_real 5
    norm_num at hc
    exact_mod_cast hc
  have hb : b 5=15 := by
    have hc := bottom_card_real 5
    norm_num at hc
    exact_mod_cast hc
  let π : Edge 5 ≃ Fin 10 := (Fintype.equivFin (Edge 5)).trans (finCongr ha)
  let σ : BottomSlot 5 ≃ Fin 15 := (Fintype.equivFin (BottomSlot 5)).trans (finCongr hb)
  have ht : (∑ z : Edge 5, (u+v+h (π z)))=10*(u+v)+∑ i,h i := by
    rw [π.sum_comp (fun i => u+v+h i)]
    simp [sum_add_distrib]
    ring
  have hb' : (∑ z : BottomSlot 5, (u-d (σ z)))=15*u-∑ i,d i := by
    rw [σ.sum_comp (fun i => u-d i)]
    simp [sum_sub_distrib]
  have hpos := (hf π σ).dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have hcharge : 0 ≤ UniformSchmidtDefectMoment.uniformCharge (family u v h d π σ) := by
    simpa [UniformSchmidtDefectMoment.uniformCharge,UniformSchmidtDefectMoment.rowSum,
      dotProduct,mulVec] using hpos
  unfold family at hcharge
  rw [K_charge,ht,hb'] at hcharge
  linarith only [hcharge]

def balanced (p : Fin 4 → ℝ) : Fin 5 → ℝ :=
  Fin.cases ((Real.sqrt 2)⁻¹) (fun i => p i/(Real.sqrt 2))
def coefficient (p : Fin 4 → ℝ) : Fin 15 → ℝ :=
  ![1,(p 0)^2,(p 1)^2,(p 2)^2,(p 3)^2,
    p 0,p 1,p 2,p 3,p 0*p 1,p 0*p 2,p 0*p 3,p 1*p 2,p 1*p 3,p 2*p 3]

private theorem fin_cases_five (p : Fin 4 → ℝ) :
    (Fin.cases 1 p : Fin 5 → ℝ) = ![1,p 0,p 1,p 2,p 3] := by
  funext i
  fin_cases i <;> rfl

private theorem balanced_mul (p : Fin 4 → ℝ) (i j : Fin 5) :
    2*balanced p i*balanced p j = (Fin.cases 1 p i)*(Fin.cases 1 p j) := by
  have hb (k : Fin 5) : balanced p k = Fin.cases 1 p k / Real.sqrt 2 := by
    refine Fin.cases ?_ (fun _ => ?_) k <;> simp [balanced,one_div]
  rw [hb,hb]
  calc
    2*(Fin.cases 1 p i / Real.sqrt 2)*(Fin.cases 1 p j / Real.sqrt 2) =
        2*((Fin.cases 1 p i)*(Fin.cases 1 p j)/(Real.sqrt 2*Real.sqrt 2)) := by
      rw [mul_assoc,div_mul_div_comm]
    _ = _ := by
      rw [← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring

private theorem balanced_diag (p : Fin 4 → ℝ) (i : Fin 5) :
    2*(balanced p i)^2=(Fin.cases 1 p i)^2 := by
  nlinarith only [balanced_mul p i i]

private theorem balanced_norm (p : Fin 4 → ℝ) (hp : ∑ i,(p i)^2=1) :
    ∑ i,(balanced p i)^2=1 := by
  have hs : 2*(∑ i : Fin 5,(balanced p i)^2) = 1+∑ i,(p i)^2 := by
    rw [mul_sum]
    simp_rw [balanced_diag]
    simp [Fin.sum_univ_succ]
  linarith only [hs,hp]

/-- Five DISTINCT tail slots, including all coordinate-zero cases. -/
theorem five_coefficient_mass (p : Fin 4 → ℝ) (hp : ∀ i,0 ≤ p i)
    (ho : Antitone p) (hn : ∑ i,(p i)^2=1) :
    ∃ S : Finset (Fin 15), S.card=5 ∧ 5/2 ≤ ∑ i ∈ S,coefficient p i := by
  classical
  have hn' : (p 0)^2+(p 1)^2+(p 2)^2+(p 3)^2=1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hn
  have h01 : p 1 ≤ p 0 := ho (by decide)
  have h02 : p 2 ≤ p 0 := ho (by decide)
  have h03 : p 3 ≤ p 0 := ho (by decide)
  by_cases hsum : 3/2 ≤ p 0+p 1+p 2+p 3
  · refine ⟨{0,5,6,7,8},by decide,?_⟩
    simp [coefficient]
    linarith
  · have htop : 2/3 < p 0 := by
      have h1 := mul_nonneg (hp 1) (sub_nonneg.mpr h01)
      have h2 := mul_nonneg (hp 2) (sub_nonneg.mpr h02)
      have h3 := mul_nonneg (hp 3) (sub_nonneg.mpr h03)
      by_contra hm
      have hprod := mul_nonneg (show 0 ≤ 2/3-p 0 by linarith)
        (show 0 ≤ p 0+p 1+p 2+p 3 by linarith [hp 0,hp 1,hp 2,hp 3])
      nlinarith [hp 0]
    refine ⟨{0,1,5,6,7},by decide,?_⟩
    norm_num [coefficient]
    by_cases hm : 5/6 ≤ p 0
    · nlinarith [hp 1,hp 2,sq_nonneg (p 0-5/6)]
    · have h13 : p 3 ≤ p 1 := ho (by decide)
      have h23 : p 3 ≤ p 2 := ho (by decide)
      have hprod := mul_le_mul h13 h23 (hp 3) (hp 1)
      have hrest : 1/2 ≤ p 1+p 2 := by
        have hA : (p 0)^2 < (5/6:ℝ)^2 :=
          (sq_lt_sq₀ (hp 0) (by norm_num)).mpr (lt_of_not_ge hm)
        by_contra hs
        have hB : (p 1+p 2)^2 < (1/2:ℝ)^2 :=
          (sq_lt_sq₀ (add_nonneg (hp 1) (hp 2)) (by norm_num)).mpr
            (lt_of_not_ge hs)
        nlinarith only [hn',hprod,hA,hB,mul_nonneg (hp 1) (hp 2)]
      nlinarith [sq_nonneg (p 0-2/3)]

/-- The exact polynomial paying all six non-star head edges. -/
theorem star_polynomial (delta B C : ℝ) :
    (6*delta^2+3*delta*B+C)^2-
      9*delta^2*(4*delta^2+2*delta*B+B^2-2*C) =
      18*delta^3*B+30*delta^2*C+6*delta*B*C+C^2 := by ring

/-- No division by the fourth largest weight delta. -/
theorem star_product_bound (delta B C P t : ℝ)
    (hd : 0 ≤ delta) (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P) (ht : 0 ≤ t)
    (hPe : P=6*delta^2+3*delta*B+C)
    (hte : t^2=4*delta^2+2*delta*B+B^2-2*C) : 3*delta*t ≤ P := by
  have hid := star_polynomial delta B C
  have hnon : 0 ≤ 18*delta^3*B+30*delta^2*C+6*delta*B*C+C^2 := by positivity
  have hscale := congrArg (fun z : ℝ => 9*delta^2*z) hte
  have hsq : (3*delta*t)^2 ≤ P^2 := by
    rw [hPe]
    nlinarith only [hid,hscale,hnon]
  nlinarith [mul_nonneg hd ht]

/-- The entire ten-edge square root, not only the four star-edge squares. -/
theorem star_gain (t R Q delta P : ℝ) (ht : 0 < t) (hR : 0 ≤ R)
    (hQ : 0 ≤ Q) (hd : 0 ≤ delta) (hQP : Q ≤ delta*R)
    (hP : 3*delta*t ≤ P) :
    Real.sqrt (t^2+Q) ≤ t+R*P/(6*t^2) := by
  have hm := mul_le_mul_of_nonneg_left hP hR
  have hm' := mul_le_mul_of_nonneg_left hQP (show 0 ≤ 3*t by positivity)
  have hden : 0 < 6*t^2 := by positivity
  have hdiv : Q/(2*t) ≤ R*P/(6*t^2) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    have hQR : 3*t*Q ≤ R*P := by nlinarith only [hm,hm']
    have hscaled := mul_le_mul_of_nonneg_right hQR (show 0 ≤ 2*t by positivity)
    nlinarith only [hscaled]
  have hs : Real.sqrt (t^2+Q) ≤ t+Q/(2*t) := by
    have ht0 := ne_of_gt ht
    have hroot := Real.sq_sqrt (show 0 ≤ t^2+Q by positivity)
    have hterm : 0 ≤ Q/(2*t) := by positivity
    have hprod : (2*t)*(Q/(2*t))=Q := by field_simp <;> ring
    nlinarith [Real.sqrt_nonneg (t^2+Q),sq_nonneg (Q/(2*t))]
  exact hs.trans (add_le_add le_rfl hdiv)

/-- The capped mass comparison includes ALL fifteen tail entries. -/
theorem capped_tail_squares (u : ℝ) (d : Fin 15 → ℝ)
    (hu : 0 ≤ u) (hd : ∀ i,0 ≤ d i) (hdu : ∀ i,d i ≤ u)
    (ho : Antitone d) (hm : ∑ i,d i ≤ 5*u) :
    (∑ i,(d i)^2) ≤ u*(∑ i,if i.val < 5 then d i else 0) := by
  let a := d 4
  have ha : 0 ≤ a := hd 4
  have hterm (i : Fin 15) : (d i)^2 ≤
      u*(if i.val < 5 then d i else 0)+a*d i-a*u*(if i.val < 5 then 1 else 0) := by
    by_cases hi : i.val < 5
    · have hia : a ≤ d i := ho (by change i.val ≤ 4; omega)
      have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hia) (sub_nonpos.mpr (hdu i))
      simp only [if_pos hi]
      nlinarith only [hp]
    · have hia : d i ≤ a := ho (by change 4 ≤ i.val; omega)
      have hp := mul_nonneg (hd i) (sub_nonneg.mpr hia)
      simp only [if_neg hi]
      nlinarith only [hp]
  have hc : (∑ i : Fin 15,if i.val < 5 then (1:ℝ) else 0)=5 := by
    simp only [Fin.sum_univ_succ]
    norm_num
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 15))) => hterm i)
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum] at hs
  rw [hc] at hs
  have hp := mul_nonneg ha (sub_nonneg.mpr hm)
  nlinarith only [hs,hp]

/-- Ten edge labels, four centre edges followed by all six leaf edges. -/
private def edgeAt : Fin 10 → Edge 5 :=
  ![⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,
    ⟨(0,4),by decide⟩,⟨(1,2),by decide⟩,⟨(1,3),by decide⟩,
    ⟨(1,4),by decide⟩,⟨(2,3),by decide⟩,⟨(2,4),by decide⟩,
    ⟨(3,4),by decide⟩]

private def edgeEquiv : Fin 10 ≃ Edge 5 :=
  Equiv.ofBijective edgeAt (by decide)

private def edgeSlots : Edge 5 ≃ Fin 10 := edgeEquiv.symm

private def tailSlots : BottomSlot 5 ≃ Fin 15 :=
  (Equiv.sumCongr (Equiv.refl (Fin 5)) edgeSlots).trans finSumFinEquiv

/-- A finite same-vector coupling witness. The tail placement is ONE fixed
assignment while all head placements in the average vary independently. -/
structure CouplingWitness (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) where
  p : Fin 4 → ℝ
  p_nonneg : ∀ i,0 ≤ p i
  p_unit : ∑ i,(p i)^2=1
  tail : BottomSlot 5 ≃ Fin 15
  weights : (Edge 5 ≃ Fin 10) → ℝ
  weights_nonneg : ∀ π,0 ≤ weights π
  weights_sum : ∑ π,weights π=1
  head_lower : Real.sqrt (∑ i,(v+h i)^2) ≤
    ∑ π,weights π*(∑ e : Edge 5,2*(v+h (π e))*balanced p e.val.1*balanced p e.val.2)
  tail_lower : (∑ i,(d i)^2)/(2*u) ≤
    (∑ i : Fin 5,2*d (tail (.inl i))*(balanced p i)^2)+
    ∑ e : Edge 5,2*d (tail (.inr e))*balanced p e.val.1*balanced p e.val.2

/-- This proves the COUPLING step, not existence of the witness. -/
theorem same_vector_coupling (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (hf : FullPSD u v h d) (w : CouplingWitness u v h d) :
    Real.sqrt (∑ i,(v+h i)^2)+(∑ i,(d i)^2)/(2*u) ≤ 2*u := by
  classical
  let x := balanced w.p
  let A := fun π : Edge 5 ≃ Fin 10 =>
    ∑ e : Edge 5,2*(v+h (π e))*x e.val.1*x e.val.2
  let T := (∑ i : Fin 5,2*d (w.tail (.inl i))*(x i)^2)+
    ∑ e : Edge 5,2*d (w.tail (.inr e))*x e.val.1*x e.val.2
  have hnorm : ∑ i,(x i)^2=1 := balanced_norm w.p w.p_unit
  have htest (π : Edge 5 ≃ Fin 10) : A π+T ≤ 2*u := by
    have hpos := (hf π w.tail).dotProduct_mulVec_nonneg x
    have hid : x ⬝ᵥ (family u v h d π w.tail)*ᵥ x =
        2*u*(∑ i,(x i)^2)-A π-T := by
      simp only [family,K,A,T,dotProduct,mulVec]
      simp_rw [← edgeEquiv.sum_comp]
      norm_num [Fin.sum_univ_succ,edgeEquiv,edgeAt,edge]
      <;> ring
    simp only [star_trivial] at hpos
    rw [hid,hnorm] at hpos
    linarith
  have hsum := sum_le_sum (fun π (_ : π ∈ (univ : Finset (Edge 5 ≃ Fin 10))) =>
    mul_le_mul_of_nonneg_left (htest π) (w.weights_nonneg π))
  simp only [mul_add,sum_add_distrib,← sum_mul,w.weights_sum,one_mul] at hsum
  dsimp [x,A,T] at *
  linarith [w.head_lower,w.tail_lower]

/-- The original full-domain existence interface. -/
def BalancedStarExistenceGap : Prop :=
  ∀ (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ),
    0 < u → 0 ≤ v → (∀ i,0 ≤ h i) → (∀ i,0 ≤ d i) →
    (∀ i,d i ≤ u) → (∑ i,d i ≤ 5*u) → FullPSD u v h d →
    Nonempty (CouplingWitness u v h d)

/- All helpers below are consumed by balancedStarExistence. Sorting is on
labelled tuples (Tuple.sort), never on a finset of numerical values. -/
private def descending {n : ℕ} (f : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -f i)

private theorem descending_antitone {n : ℕ} (f : Fin n → ℝ) :
    Antitone (fun i => f (descending f i)) := by
  intro i j hij
  have hh := Tuple.monotone_sort (fun i => -f i) hij
  change -f (descending f i) ≤ -f (descending f j) at hh
  linarith only [hh]

private def cycle (n : ℕ) [NeZero n] (k : Fin n) : Equiv.Perm (Fin n) where
  toFun i := i+k
  invFun i := i-k
  left_inv i := by simp
  right_inv i := by simp

/-- Exact labelled cyclic assignment identity, independent of inequalities. -/
private theorem cyclic_sum (n : ℕ) [NeZero n] (a c : Fin n → ℝ) :
    (∑ k : Fin n, ∑ i : Fin n, a (i+k)*c i) = (∑ i,a i)*(∑ i,c i) := by
  rw [sum_comm]
  simp_rw [← sum_mul]
  have hshift (i : Fin n) : (∑ k : Fin n,a (i+k)) = ∑ k,a k := by
    have hs := Equiv.sum_comp (cycle n i) a
    change (∑ k, a (k+i)) = ∑ k, a k at hs
    simpa only [add_comm] using hs
  simp_rw [hshift]
  rw [mul_sum]

private theorem good_cycle (n : ℕ) [NeZero n] (a c : Fin n → ℝ) (b : ℝ)
    (hb : (n:ℝ)*b ≤ (∑ i,a i)*(∑ i,c i)) :
    ∃ k : Fin n, b ≤ ∑ i : Fin n,a (i+k)*c i := by
  classical
  obtain ⟨k, _, hk⟩ := exists_max_image (univ : Finset (Fin n))
    (fun k => ∑ i : Fin n,a (i+k)*c i) univ_nonempty
  refine ⟨k,?_⟩
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => hk j (mem_univ j))
  rw [cyclic_sum] at hs
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hn : (0:ℝ)<n := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (mul_le_mul_iff_right₀ hn).mp (hb.trans hs)

private def leafCoefficient (p : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![p 0*p 1,p 0*p 2,p 0*p 3,p 1*p 2,p 1*p 3,p 2*p 3]

private theorem leaf_nonneg (p : Fin 4 → ℝ) (hp : ∀ i,0 ≤ p i) :
    ∀ i,0 ≤ leafCoefficient p i := by
  intro i
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  fin_cases i <;> norm_num [leafCoefficient] <;> positivity

private theorem coefficient_nonneg (p : Fin 4 → ℝ) (hp : ∀ i,0 ≤ p i) :
    ∀ i,0 ≤ coefficient p i := by
  intro i
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  fin_cases i <;> norm_num [coefficient] <;> positivity

private def headValue (a : Fin 10 → ℝ) (p : Fin 4 → ℝ)
    (π : Edge 5 ≃ Fin 10) : ℝ :=
  ∑ e : Edge 5,2*a (π e)*balanced p e.val.1*balanced p e.val.2

private def tailValue (d : Fin 15 → ℝ) (p : Fin 4 → ℝ)
    (σ : BottomSlot 5 ≃ Fin 15) : ℝ :=
  (∑ i : Fin 5,2*d (σ (.inl i))*(balanced p i)^2)+
    ∑ e : Edge 5,2*d (σ (.inr e))*balanced p e.val.1*balanced p e.val.2

private theorem head_slots (a : Fin 10 → ℝ) (p : Fin 4 → ℝ)
    (τ : Equiv.Perm (Fin 10)) :
    headValue a p (edgeSlots.trans τ) =
      (∑ i : Fin 4,a (τ (Fin.castAdd 6 i))*p i)+
      ∑ i : Fin 6,a (τ (Fin.natAdd 4 i))*leafCoefficient p i := by
  unfold headValue
  have he (e : Edge 5) :
      2*a ((edgeSlots.trans τ) e)*balanced p e.val.1*balanced p e.val.2 =
      a ((edgeSlots.trans τ) e)*
        ((Fin.cases 1 p e.val.1)*(Fin.cases 1 p e.val.2)) := by
    rw [← balanced_mul]
    ring
  simp_rw [he]
  rw [← edgeEquiv.sum_comp]
  simp only [Equiv.trans_apply,edgeSlots,Equiv.symm_apply_apply]
  simp [edgeEquiv,edgeAt,leafCoefficient,Fin.sum_univ_succ,fin_cases_five] <;> ring

private theorem coefficient_slot (p : Fin 4 → ℝ) (b : BottomSlot 5) :
    coefficient p (tailSlots b) =
      Sum.elim (fun i : Fin 5 => (Fin.cases 1 p i)^2)
        (fun e : Edge 5 => (Fin.cases 1 p e.val.1)*(Fin.cases 1 p e.val.2)) b := by
  rcases b with i | e
  · change coefficient p (Fin.castAdd 10 i) = (Fin.cases 1 p i)^2
    fin_cases i <;> simp [coefficient, fin_cases_five]
  · obtain ⟨i,rfl⟩ := edgeEquiv.surjective e
    change coefficient p (Fin.natAdd 5 (edgeSlots (edgeEquiv i))) = _
    simp only [edgeSlots,Equiv.symm_apply_apply]
    fin_cases i <;> simp [edgeEquiv,edgeAt,coefficient, fin_cases_five]

private theorem tail_slots (d : Fin 15 → ℝ) (p : Fin 4 → ℝ)
    (τ : Equiv.Perm (Fin 15)) :
    tailValue d p (tailSlots.trans τ) = ∑ i : Fin 15,d (τ i)*coefficient p i := by
  rw [← tailSlots.sum_comp (fun i => d (τ i)*coefficient p i)]
  rw [Fintype.sum_sum_type]
  unfold tailValue
  congr 1
  · apply sum_congr rfl
    intro i _
    rw [coefficient_slot]
    simp only [Sum.elim_inl,Equiv.trans_apply]
    rw [← balanced_diag]
    ring
  · apply sum_congr rfl
    intro e _
    rw [coefficient_slot]
    simp only [Sum.elim_inr,Equiv.trans_apply]
    rw [← balanced_mul]
    ring

/-- Enumerate a selected five-element set and its ten-element complement.
No numerical distinctness, positivity, or nonzero entries are used. -/
private def selectedSlots (S : Finset (Fin 15)) (hS : S.card=5) :
    Fin 5 ⊕ Fin 10 ≃ Fin 15 := by
  classical
  let es : S ≃ Fin 5 := S.equivFinOfCardEq hS
  let ec : (Sᶜ : Finset (Fin 15)) ≃ Fin 10 :=
    (Sᶜ).equivFinOfCardEq (by simp [card_compl,hS])
  let f : Fin 5 ⊕ Fin 10 → Fin 15 :=
    Sum.elim (fun i => (es.symm i).val) (fun i => (ec.symm i).val)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · exact congrArg Sum.inl (es.symm.injective (Subtype.ext hxy))
    · change (es.symm i).val=(ec.symm j).val at hxy
      exact ((mem_compl.mp (ec.symm j).property)
        (hxy ▸ (es.symm i).property)).elim
    · change (ec.symm i).val=(es.symm j).val at hxy
      exact ((mem_compl.mp (ec.symm i).property)
        (hxy.symm ▸ (es.symm j).property)).elim
    · exact congrArg Sum.inr (ec.symm.injective (Subtype.ext hxy))
  · intro x
    by_cases hx : x ∈ S
    · refine ⟨.inl (es ⟨x,hx⟩),?_⟩
      simp [f]
    · refine ⟨.inr (ec ⟨x,mem_compl.mpr hx⟩),?_⟩
      simp [f]

private theorem selected_sum (S : Finset (Fin 15)) (hS : S.card=5)
    (c : Fin 15 → ℝ) :
    (∑ i : Fin 5,c (selectedSlots S hS (.inl i)))=∑ i ∈ S,c i := by
  classical
  let es : S ≃ Fin 5 := S.equivFinOfCardEq hS
  change (∑ i : Fin 5,c (es.symm i).val)=_
  rw [es.symm.sum_comp (fun i : S => c i.val),sum_coe_sort]

private theorem tail_exists (u : ℝ) (d : Fin 15 → ℝ) (p : Fin 4 → ℝ)
    (hu : 0<u) (hd : ∀ i,0 ≤ d i) (hdu : ∀ i,d i ≤ u)
    (hm : ∑ i,d i ≤ 5*u) (hp : ∀ i,0 ≤ p i) (ho : Antitone p)
    (hn : ∑ i,(p i)^2=1) :
    ∃ σ : BottomSlot 5 ≃ Fin 15,
      (∑ i,(d i)^2)/(2*u) ≤ tailValue d p σ ∧
      ∀ σ',tailValue d p σ' ≤ tailValue d p σ := by
  classical
  let s := descending d
  let ds : Fin 15 → ℝ := fun i => d (s i)
  have hds : ∀ i,0 ≤ ds i := fun i => hd (s i)
  have hmass : ∑ i,ds i ≤ 5*u := by
    change (∑ i, d (s i)) ≤ 5*u
    rw [Equiv.sum_comp]
    exact hm
  have hcap := capped_tail_squares u ds hu.le hds
    (fun i => hdu (s i)) (descending_antitone d) hmass
  let top : ℝ := ∑ i : Fin 5,ds (Fin.castAdd 10 i)
  have htop : 0 ≤ top := sum_nonneg (fun i _ => hds _)
  have htop_eq : (∑ i : Fin 15,if i.val<5 then ds i else 0)=top := by
    simp [top,Fin.sum_univ_succ]
  have hbound : (∑ i,(d i)^2)/(2*u) ≤ top/2 := by
    have hs : (∑ i,(ds i)^2) = ∑ i,(d i)^2 := Equiv.sum_comp s (fun i => (d i)^2)
    rw [hs,htop_eq] at hcap
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*u)).mpr
    nlinarith only [hcap]
  obtain ⟨S,hS,hcoeff⟩ := five_coefficient_mass p hp ho hn
  let q := selectedSlots S hS
  have hcs : 5/2 ≤ ∑ i : Fin 5,coefficient p (q (.inl i)) := by
    simpa only [q,selected_sum] using hcoeff
  have hav : (5:ℝ)*(top/2) ≤ top*(∑ i : Fin 5,coefficient p (q (.inl i))) := by
    nlinarith only [mul_nonneg htop (sub_nonneg.mpr hcs)]
  obtain ⟨k,hk⟩ := good_cycle 5 (fun i => ds (Fin.castAdd 10 i))
    (fun i => coefficient p (q (.inl i))) (top/2) hav
  let τ : Equiv.Perm (Fin 15) := q.symm.trans
    ((Equiv.sumCongr (cycle 5 k) (Equiv.refl (Fin 10))).trans
      (finSumFinEquiv.trans s))
  have hv : tailValue d p (tailSlots.trans τ) =
      (∑ i : Fin 5,ds (Fin.castAdd 10 (i+k))*coefficient p (q (.inl i)))+
      ∑ i : Fin 10,ds (Fin.natAdd 5 i)*coefficient p (q (.inr i)) := by
    rw [tail_slots,← q.sum_comp (fun i => d (τ i)*coefficient p i)]
    simp [τ,ds,cycle,Fintype.sum_sum_type,
      finSumFinEquiv_apply_left (m:=5) (n:=10),
      finSumFinEquiv_apply_right (m:=5) (n:=10)]
  have hrest : 0 ≤ ∑ i : Fin 10,ds (Fin.natAdd 5 i)*coefficient p (q (.inr i)) :=
    sum_nonneg (fun i _ => mul_nonneg (hds _) (coefficient_nonneg p hp _))
  have hgood : (∑ i,(d i)^2)/(2*u) ≤ tailValue d p (tailSlots.trans τ) := by
    rw [hv]
    linarith only [hbound,hk,hrest]
  letI : Nonempty (BottomSlot 5 ≃ Fin 15) := ⟨tailSlots.trans τ⟩
  obtain ⟨σ,_,hσ⟩ := exists_max_image (univ : Finset (BottomSlot 5 ≃ Fin 15))
    (tailValue d p) univ_nonempty
  exact ⟨σ,hgood.trans (hσ _ (mem_univ _)),fun σ' => hσ σ' (mem_univ σ')⟩

private def rotateLeaves (k : Fin 6) : Equiv.Perm (Fin 10) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 4)) (cycle 6 k)).trans finSumFinEquiv)

private theorem head_exists (a : Fin 10 → ℝ) (ha : ∀ i,0 ≤ a i) :
    ∃ (p : Fin 4 → ℝ) (π : Edge 5 ≃ Fin 10),
      (∀ i,0 ≤ p i) ∧ Antitone p ∧ (∑ i,(p i)^2=1) ∧
      Real.sqrt (∑ i,(a i)^2) ≤ headValue a p π := by
  classical
  let s := descending a
  let w : Fin 10 → ℝ := fun i => a (s i)
  have hw : ∀ i,0 ≤ w i := fun i => ha (s i)
  have hwo : Antitone w := descending_antitone a
  have hsum : (∑ i,(w i)^2)=∑ i,(a i)^2 := Equiv.sum_comp s (fun i => (a i)^2)
  by_cases hF : (∑ i,(a i)^2)=0
  · have hz (i : Fin 10) : a i=0 := by
      have hi : (a i)^2 ≤ ∑ j,(a j)^2 :=
        single_le_sum (fun j _ => sq_nonneg (a j)) (mem_univ i)
      rw [hF] at hi
      exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg (a i)))
    refine ⟨![1,0,0,0],edgeSlots.trans s,?_,?_,?_,?_⟩
    · intro i; fin_cases i <;> norm_num
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at *
    · norm_num [Fin.sum_univ_succ]
    · simp [hF,headValue,hz]
  · have hzero : 0<w 0 := by
      by_contra hh
      have hw0 : w 0=0 := le_antisymm (le_of_not_gt hh) (hw 0)
      have hz (i : Fin 10) : w i=0 :=
        le_antisymm (by simpa [hw0] using hwo (show (0:Fin 10) ≤ i from Fin.zero_le i)) (hw i)
      have : (∑ i,(w i)^2)=0 := by simp [hz]
      exact hF (hsum.symm.trans this)
    let A : Fin 4 → ℝ := fun i => w (Fin.castAdd 6 i)
    let t : ℝ := Real.sqrt (∑ i,(A i)^2)
    have hA : ∀ i,0 ≤ A i := fun i => hw _
    have ht2 : t^2=∑ i,(A i)^2 := Real.sq_sqrt (sum_nonneg (fun i _ => sq_nonneg _))
    have ht : 0<t := by
      apply Real.sqrt_pos.mpr
      have hs : (A 0)^2 ≤ ∑ i,(A i)^2 :=
        single_le_sum (fun i _ => sq_nonneg (A i)) (mem_univ 0)
      have hA0 : 0<A 0 := hzero
      exact (sq_pos_of_pos hA0).trans_le hs
    let p : Fin 4 → ℝ := fun i => A i/t
    have hp : ∀ i,0 ≤ p i := fun i => div_nonneg (hA i) ht.le
    have hpo : Antitone p := by
      intro i j hij
      exact div_le_div_of_nonneg_right (hwo (show Fin.castAdd 6 i ≤ Fin.castAdd 6 j from hij)) ht.le
    have hpn : ∑ i,(p i)^2=1 := by
      change (∑ i,(A i/t)^2)=1
      simp_rw [div_pow]
      rw [← sum_div,← ht2,div_self (pow_ne_zero 2 (ne_of_gt ht))]
    let delta := w 3
    let R : ℝ := ∑ i : Fin 6,w (Fin.natAdd 4 i)
    let Q : ℝ := ∑ i : Fin 6,(w (Fin.natAdd 4 i))^2
    let P : ℝ := ∑ i : Fin 6,leafCoefficient A i
    have hd : 0 ≤ delta := hw 3
    have hR : 0 ≤ R := sum_nonneg (fun i _ => hw _)
    have hQ : 0 ≤ Q := sum_nonneg (fun i _ => sq_nonneg _)
    have hP0 : 0 ≤ P := sum_nonneg (fun i _ => leaf_nonneg A hA i)
    have hQP : Q ≤ delta*R := by
      have hterm (i : Fin 6) : (w (Fin.natAdd 4 i))^2 ≤ delta*w (Fin.natAdd 4 i) := by
        have hi : w (Fin.natAdd 4 i) ≤ delta := hwo (by change 3 ≤ 4+i.val; omega)
        nlinarith only [mul_nonneg (hw (Fin.natAdd 4 i)) (sub_nonneg.mpr hi)]
      simpa only [Q,R,mul_sum] using sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 6))) => hterm i)
    let b : Fin 4 → ℝ := fun i => A i-delta
    let B : ℝ := ∑ i,b i
    let C : ℝ := ∑ i : Fin 6,leafCoefficient b i
    have hb : ∀ i,0 ≤ b i := by
      intro i
      apply sub_nonneg.mpr
      exact hwo (by change i.val ≤ 3; omega)
    have hB : 0 ≤ B := sum_nonneg (fun i _ => hb i)
    have hC : 0 ≤ C := sum_nonneg (fun i _ => leaf_nonneg b hb i)
    have hPe : P=6*delta^2+3*delta*B+C := by
      simp [P,B,C,b,leafCoefficient,Fin.sum_univ_succ]
      ring
    have hte : t^2=4*delta^2+2*delta*B+B^2-2*C := by
      rw [ht2]
      simp [B,C,b,leafCoefficient,Fin.sum_univ_succ]
      ring
    have hP := star_product_bound delta B C P t hd hB hC hP0 ht.le hPe hte
    have hg := star_gain t R Q delta P ht hR hQ hd hQP hP
    have hstar : (∑ i : Fin 4,A i*p i)=t := by
      calc
        (∑ i : Fin 4,A i*p i) = (∑ i : Fin 4,(A i)^2)/t := by
          rw [sum_div]
          apply sum_congr rfl
          intro i _
          dsimp [p]
          ring
        _ = t := by rw [← ht2]; field_simp [ne_of_gt ht] <;> ring
    have hleaf : (∑ i : Fin 6,leafCoefficient p i)=P/t^2 := by
      simp [p,P,leafCoefficient,Fin.sum_univ_succ]
      ring
    have hav : (6:ℝ)*(R*P/(6*t^2)) ≤
        R*(∑ i : Fin 6,leafCoefficient p i) := by
      rw [hleaf]
      apply le_of_eq
      field_simp [ne_of_gt ht] <;> ring
    obtain ⟨k,hk⟩ := good_cycle 6 (fun i => w (Fin.natAdd 4 i))
      (leafCoefficient p) (R*P/(6*t^2)) hav
    let π := edgeSlots.trans ((rotateLeaves k).trans s)
    have hv : headValue a p π = t+
        ∑ i : Fin 6,w (Fin.natAdd 4 (i+k))*leafCoefficient p i := by
      dsimp only [π]
      rw [head_slots]
      simpa [rotateLeaves,cycle,w,A,
          finSumFinEquiv_symm_apply_castAdd (m:=4) (n:=6),
          finSumFinEquiv_symm_apply_natAdd (m:=4) (n:=6),
          finSumFinEquiv_apply_left (m:=4) (n:=6),
          finSumFinEquiv_apply_right (m:=4) (n:=6)] using congrArg
          (fun z => z+∑ i : Fin 6,w (Fin.natAdd 4 (i+k))*leafCoefficient p i) hstar
    have hFsplit : (∑ i,(a i)^2)=t^2+Q := by
      rw [← hsum,Fin.sum_univ_add (a:=4) (b:=6)]
      rw [ht2]
    refine ⟨p,π,hp,hpo,hpn,?_⟩
    rw [hFsplit,hv]
    exact hg.trans (add_le_add le_rfl hk)

/-- Construct the original same-vector witness, including all labelled
assignments in the probability domain. Its mass is a Dirac mass at a good
head assignment; the tail is a maximizer chosen at this very same p. -/
theorem balancedStarExistence : BalancedStarExistenceGap := by
  classical
  intro u v h d hu hv hh hd hdu hm _hf
  obtain ⟨p,π,hp,hpo,hpn,hhead⟩ := head_exists (fun i => v+h i)
    (fun i => add_nonneg hv (hh i))
  obtain ⟨σ,htail,_hmax⟩ := tail_exists u d p hu hd hdu hm hp hpo hpn
  refine ⟨{
    p := p
    p_nonneg := hp
    p_unit := hpn
    tail := σ
    weights := fun π' => if π'=π then 1 else 0
    weights_nonneg := ?_
    weights_sum := ?_
    head_lower := ?_
    tail_lower := htail
  }⟩
  · intro π'
    split_ifs <;> norm_num
  · simp
  · simpa [headValue] using hhead

/-- Uniform tail charge at a fixed balanced vector. Only fifteen cyclic
placements are used to lower-bound the maximum over all labelled placements. -/
private theorem tail_uniform_charge (d : Fin 15 → ℝ) (p : Fin 4 → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hp : ∀ i, 0 ≤ p i)
    (hn : ∑ i, (p i)^2 = 1)
    (σ : BottomSlot 5 ≃ Fin 15)
    (hmax : ∀ σ', tailValue d p σ' ≤ tailValue d p σ) :
    (∑ i, d i)/5 ≤ tailValue d p σ := by
  let s : ℝ := ∑ i, p i
  have hs : 0 ≤ s := sum_nonneg (fun i _ => hp i)
  have hss : 1 ≤ s^2 := by
    simpa only [hn] using sum_sq_le_sq_sum_of_nonneg
      (s := (univ : Finset (Fin 4))) (fun i _ => hp i)
  have hs1 : 1 ≤ s := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1) hs).mp (by simpa using hss)
  have hc : 3 ≤ ∑ i, coefficient p i := by
    have he : (∑ i, coefficient p i) = 1 + (1+s)^2/2 := by
      dsimp [s]
      simp only [coefficient, Fin.sum_univ_succ] at hn ⊢
      norm_num at hn ⊢
      nlinarith only [hn]
    rw [he]
    nlinarith only [hs1, hss]
  have hD : 0 ≤ ∑ i, d i := sum_nonneg (fun i _ => hd i)
  obtain ⟨k,hk⟩ := good_cycle 15 d (coefficient p) ((∑ i,d i)/5)
    (by nlinarith only [mul_nonneg hD (sub_nonneg.mpr hc)])
  have he : tailValue d p (tailSlots.trans (cycle 15 k)) =
      ∑ i : Fin 15, d (i+k)*coefficient p i := by
    rw [tail_slots]
    rfl
  exact hk.trans (he ▸ hmax (tailSlots.trans (cycle 15 k)))

/-- Both charges use the very same balanced vector and maximizing tail
placement. No averaging of independently chosen marginal witnesses occurs. -/
theorem family_star_charges (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (hu : 0 < u) (hv : 0 ≤ v) (hh : ∀ i, 0 ≤ h i)
    (hd : ∀ i, 0 ≤ d i) (hdu : ∀ i, d i ≤ u)
    (hm : ∑ i, d i ≤ 5*u) (hf : FullPSD u v h d) :
    Real.sqrt (∑ i, (v+h i)^2) + (∑ i, (d i)^2)/(2*u) ≤ 2*u ∧
    Real.sqrt (∑ i, (v+h i)^2) + (∑ i, d i)/5 ≤ 2*u := by
  obtain ⟨p,π,hp,hpo,hpn,hhead⟩ := head_exists (fun i => v+h i)
    (fun i => add_nonneg hv (hh i))
  obtain ⟨σ,htail,hmax⟩ := tail_exists u d p hu hd hdu hm hp hpo hpn
  have hlinear := tail_uniform_charge d p hd hp hpn σ hmax
  have htest : headValue (fun i => v+h i) p π + tailValue d p σ ≤ 2*u := by
    have hpos := (hf π σ).dotProduct_mulVec_nonneg (balanced p)
    have hid : balanced p ⬝ᵥ (family u v h d π σ)*ᵥ balanced p =
        2*u*(∑ i,(balanced p i)^2) -
          headValue (fun i => v+h i) p π - tailValue d p σ := by
      simp only [family,K,headValue,tailValue,dotProduct,mulVec]
      simp_rw [← edgeEquiv.sum_comp]
      norm_num [Fin.sum_univ_succ,edgeEquiv,edgeAt,edge]
      <;> ring
    simp only [star_trivial] at hpos
    rw [hid,balanced_norm p hpn] at hpos
    linarith only [hpos]
  constructor <;> linarith only [htest,hhead,htail,hlinear]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
