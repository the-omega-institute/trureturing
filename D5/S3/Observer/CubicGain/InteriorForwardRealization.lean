/- GID: D5/S3/Observer/CubicGain/InteriorForwardRealization
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/InteriorForwardRealization
   mirror-E: none(waiver:positive-interior-forward-realization)
   anchors: [mathlib/module/Mathlib.RingTheory.Coprime.Lemmas]
   utility: none
   digest: Admitted interior parameters realize one forward cumulative history. -/

import D5.S3.Observer.CubicGain.InteriorPrefixClassification
import D5.S3.Observer.TraceFibers.FixedFiberPairModulus

/-! Forward words, first-endpoint and rank filters for the interior parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace D5.S3.Observer.CubicGain.InteriorForwardRealization

open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open D5.S3.Observer.CubicGain.PrefixKernelSigns
open D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open D5.S3.Observer.CubicGain.PhaseRigidity
open D5.S3.Observer.CubicGain.InteriorNormalForm
open D5.S3.Observer.CubicGain.InteriorPrefixClassification
open scoped Matrix

/-- Repeating the chronological pair J,M executes the lower shear L. -/
def lowerWord : ℕ → List Bool
  | 0 => []
  | n+1 => lowerWord n ++ [true,false]

private theorem lower_product (n : ℕ) :
    futureProduct (lowerWord n) = !![1,0;(n:ℝ),1] := by
  induction n with
  | zero => ext i k; fin_cases i <;> fin_cases k <;> simp [lowerWord,futureProduct]
  | succ n ih =>
    rw [lowerWord,product_append,ih]
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [futureProduct,actionJ,actionM,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

def endpointDifference (A K H : Mat) : Mat →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X i := Matrix.trace ((![A,K*A,H*(K*A)] : Fin 3 → Mat) i*X)-Matrix.trace X
  map_add' X Y := by ext i; simp [Matrix.mul_add,Matrix.trace_add]; ring
  map_smul' c X := by ext i; simp [Matrix.mul_smul,Matrix.trace_smul]; ring

private theorem words_for_multipliers (Q h σ : ℤ)
    (hQ : 2 ≤ Q) (hh : 0 < h) (hσ : σ = 1 ∨ σ = -1) :
    ∃ uK uH : List Bool,
      futureProduct uK = !![1,1;(Q:ℝ),((Q+σ:ℤ):ℝ)] ∧
      futureProduct uH = !![0,1;1,(h:ℝ)] ∧
      uH = [true] ++ lowerWord h.toNat ∧
      (σ = 1 → uK = [false,true] ++ lowerWord Q.toNat) ∧
      (σ = -1 → uK = [true,false,true] ++ lowerWord (Q-1).toNat) := by
  have hQnat : (Q.toNat:ℤ) = Q := Int.toNat_of_nonneg (by omega)
  have hQnat' : ((Q-1).toNat:ℤ) = Q-1 := Int.toNat_of_nonneg (by omega)
  have hhnat : (h.toNat:ℤ) = h := Int.toNat_of_nonneg (by omega)
  have hHr : futureProduct ([true] ++ lowerWord h.toNat) = !![0,1;1,(h:ℝ)] := by
    rw [product_append,lower_product]
    have he : (h.toNat:ℝ) = h := by exact_mod_cast hhnat
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [futureProduct,actionJ,Matrix.mul_apply,Fin.sum_univ_two,he]
  rcases hσ with rfl | rfl
  · refine ⟨[false,true] ++ lowerWord Q.toNat,[true] ++ lowerWord h.toNat,?_,hHr,rfl,?_,?_⟩
    · rw [product_append,lower_product]
      have he : (Q.toNat:ℝ) = Q := by exact_mod_cast hQnat
      ext i k
      fin_cases i <;> fin_cases k <;>
        norm_num [futureProduct,actionJ,actionM,Matrix.mul_apply,Fin.sum_univ_two,he]
    · intro _; rfl
    · intro he; norm_num at he
  · refine ⟨[true,false,true] ++ lowerWord (Q-1).toNat,[true] ++ lowerWord h.toNat,?_,hHr,rfl,?_,?_⟩
    · rw [product_append,lower_product]
      have he : ((Q-1).toNat:ℝ) = (Q:ℝ)-1 := by exact_mod_cast hQnat'
      simp only [he]
      ext i k
      fin_cases i <;> fin_cases k <;>
        norm_num [futureProduct,actionJ,actionM,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
    · intro he; norm_num at he
    · intro _; rfl

/-- Every admitted integer tuple and every admitted first endpoint retain the
rank-three filter and are realized on one chronological triple of forward words. -/
theorem admitted_parameters_realize (x d m n σ : ℤ) (A : ZMat)
    (hd : 1 ≤ d) (hx : d < x) (hxd : IsCoprime x d)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hσ : σ = 1 ∨ σ = -1)
    (ha : 1 ≤ x-m*d)
    (hab : IsCoprime (x-m*d) (m*(x+(n*(x+d)+σ)*d)-d))
    (hA : ∀ i j, 0 ≤ A i j) (hdet : A.det = 1 ∨ A.det = -1)
    (hfirst : A *ᵥ ![x-m*d,-(m*(x+(n*(x+d)+σ)*d)-d)] = ![x,d])
    (hrank : Module.finrank ℝ (LinearMap.range
      (endpointDifference (real A) (!![1,1;((1+n*d:ℤ):ℝ),((1+n*d+σ:ℤ):ℝ)])
        (!![0,1;1,((n*(x+d)+σ:ℤ):ℝ)]))) = 3) :
    let a := x-m*d
    let h := n*(x+d)+σ
    let c := x+h*d
    let b := m*c-d
    let Q := 1+n*d
    ∃ (w : Fin 3 → List Bool) (p : PrimitiveCoordinates),
      (p.a:ℤ) = a ∧ (p.b:ℤ) = b ∧ (p.c:ℤ) = c ∧ (p.d:ℤ) = d ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < h ∧ 2 ≤ Q ∧
      prefixMatrix w 1 = real A ∧
      futureProduct (w 1) = !![1,1;(Q:ℝ),((Q+σ:ℤ):ℝ)] ∧
      futureProduct (w 2) = !![0,1;1,(h:ℝ)] ∧
      w 2 = [true] ++ lowerWord h.toNat ∧
      (σ = 1 → w 1 = [false,true] ++ lowerWord Q.toNat) ∧
      (σ = -1 → w 1 = [true,false,true] ++ lowerWord (Q-1).toNat) ∧
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column+
        ((![0,m,m+1,m+1+h] : Fin 4 → ℤ) i:ℝ) • p.direction) ∧
      OrientedKernelGenerator w p.matrix ∧ ParameterForm w p (![0,m,m+1,m+1+h]) ∧
      ∀ S : Mat, PositiveRankOne S → ∃ f ℓ : Fin 2 → ℝ,
        Positive f ∧ Positive ℓ ∧ S = Matrix.vecMulVec f ℓ ∧
        (∀ u : List Bool, Positive (futureProduct u *ᵥ f)) ∧
        ∀ k δ : ℝ, ∀ i : Fin 4,
          (1+(i.val:ℝ)*k)*(ℓ ⬝ᵥ (prefixMatrix w i *ᵥ f))+δ =
          (1+(i.val:ℝ)*k)*Matrix.trace (prefixMatrix w i*S)+δ := by
  dsimp only
  let a := x-m*d
  let h := n*(x+d)+σ
  let c := x+h*d
  let b := m*c-d
  let Q := 1+n*d
  have hd0 : 0 < d := by omega
  have hx0 : 0 < x := by omega
  have ha0 : 0 < a := by dsimp [a]; omega
  have hh0 : 0 < h := by
    dsimp [h]
    rcases hσ with he | he <;> rw [he] <;> nlinarith only [hn,hx,hd]
  have hcx : x < c := by dsimp [c]; nlinarith only [hh0,hd0]
  have hc0 : 0 < c := lt_trans hx0 hcx
  have hb0 : 0 < b := by dsimp [b]; nlinarith only [hm,hcx,hx,hd0]
  have hQ : 2 ≤ Q := by dsimp [Q]; nlinarith only [hn,hd]
  have hcd : IsCoprime c d := hxd.add_mul_right_left h
  have hab' : IsCoprime a b := hab
  have ht : 0 < a*c+b*d := by nlinarith only [mul_pos ha0 hc0,mul_pos hb0 hd0]
  let p : PrimitiveCoordinates := {
    a := a.toNat
    b := b.toNat
    c := c.toNat
    d := d.toNat
    column_primitive := (show IsCoprime (a.toNat:ℤ) (b.toNat:ℤ) by
      simpa [Int.toNat_of_nonneg ha0.le,Int.toNat_of_nonneg hb0.le] using hab').natCoprime
    row_primitive := (show IsCoprime (c.toNat:ℤ) (d.toNat:ℤ) by
      simpa [Int.toNat_of_nonneg hc0.le,Int.toNat_of_nonneg hd0.le] using hcd).natCoprime
    trace_pos := by
      exact_mod_cast (show (0:ℤ) < (a.toNat:ℤ)*c.toNat+(b.toNat:ℤ)*d.toNat by
        simpa [Int.toNat_of_nonneg ha0.le,Int.toNat_of_nonneg hb0.le,
          Int.toNat_of_nonneg hc0.le,Int.toNat_of_nonneg hd0.le] using ht) }
  have hpa : (p.a:ℤ) = a := Int.toNat_of_nonneg ha0.le
  have hpb : (p.b:ℤ) = b := Int.toNat_of_nonneg hb0.le
  have hpc : (p.c:ℤ) = c := Int.toNat_of_nonneg hc0.le
  have hpd : (p.d:ℤ) = d := Int.toNat_of_nonneg hd0.le
  have hpdR : (p.d:ℝ) = d := by exact_mod_cast hpd
  have hpcoords : p.column = ![(a:ℝ),-(b:ℝ)] ∧ p.direction = ![(d:ℝ),(c:ℝ)] := by
    constructor <;> ext i <;> fin_cases i <;>
      simp [PrimitiveCoordinates.column,PrimitiveCoordinates.direction] <;>
      exact_mod_cast (by first | exact hpa | exact hpb | exact hpc | exact hpd)
  obtain ⟨uA,huA⟩ := (legal_matrix_monoid (real A)).mpr ⟨fun i j =>
    ⟨by change (0:ℝ) ≤ (A i j:ℝ); exact_mod_cast hA i j,A i j,rfl⟩,by
      rcases hdet with he | he
      · left; simpa [real,Matrix.det_fin_two] using congrArg (Int.cast : ℤ → ℝ) he
      · right; simpa [real,Matrix.det_fin_two] using congrArg (Int.cast : ℤ → ℝ) he⟩
  obtain ⟨uK,uH,huK,huH,hwH,hwKplus,hwKminus⟩ := words_for_multipliers Q h σ hQ hh0 hσ
  let w : Fin 3 → List Bool := ![uA,uK,uH]
  have he1 : prefixMatrix w 1 = real A := by
    simpa [prefixMatrix,prefixWord,w,List.ofFn_succ] using huA
  have he2 : prefixMatrix w 2 = futureProduct uK*real A := by
    simpa [w,he1] using prefix_step w 1
  have he3 : prefixMatrix w 3 = futureProduct uH*(futureProduct uK*real A) := by
    simpa [w,he2] using prefix_step w 2
  have hAr : real A *ᵥ p.column = ![(x:ℝ),(d:ℝ)] := by
    rw [hpcoords.1]
    have hfirst' : A *ᵥ ![a,-b] = ![x,d] := hfirst
    ext i
    have he := congrFun hfirst' i
    fin_cases i <;> simp [real,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at he ⊢ <;>
      exact_mod_cast he
  have hQeq : Q*(x+d) = c+(1-σ)*d := by dsimp [Q,c,h]; ring
  have himages : ∀ i, prefixMatrix w i *ᵥ p.column = p.column+
      ((![0,m,m+1,m+1+h] : Fin 4 → ℤ) i:ℝ) • p.direction := by
    intro i
    fin_cases i
    · simp [prefixMatrix,prefixWord,futureProduct]
    · change prefixMatrix w 1 *ᵥ p.column = p.column+(m:ℝ) • p.direction
      rw [he1,hAr,hpcoords.1,hpcoords.2]
      ext k; fin_cases k <;> simp [a,b] <;> ring
    · change prefixMatrix w 2 *ᵥ p.column = p.column+((m+1:ℤ):ℝ) • p.direction
      rw [he2,←Matrix.mulVec_mulVec,hAr,huK,hpcoords.1,hpcoords.2]
      ext k
      fin_cases k <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      · dsimp [a]; push_cast; ring
      · have he : (Q:ℝ)*((x:ℝ)+d) = (c:ℝ)+(1-σ)*d := by exact_mod_cast hQeq
        dsimp [b]; push_cast; nlinarith only [he]
    · change prefixMatrix w 3 *ᵥ p.column = p.column+((m+1+h:ℤ):ℝ) • p.direction
      rw [he3,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hAr,huK,huH,hpcoords.1,hpcoords.2]
      ext k
      fin_cases k <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      all_goals
        have he : (Q:ℝ)*((x:ℝ)+d) = (c:ℝ)+(1-σ)*d := by exact_mod_cast hQeq
        have hec : (c:ℝ) = (x:ℝ)+h*d := by dsimp [c]; push_cast; rfl
        dsimp [a,b]; push_cast
      · linear_combination he+hec
      · linear_combination (h:ℝ)*he-hec
  have hrank' : Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3 := by
    have he : prefixDifference w = endpointDifference (real A)
        (!![1,1;(Q:ℝ),((Q+σ:ℤ):ℝ)]) (!![0,1;1,(h:ℝ)]) := by
      ext X i
      fin_cases i <;> simp [prefixDifference,endpointDifference,he1,he2,he3,huK,huH]
    rw [he]
    exact hrank
  have hG := whole_class_primitive_lattice.2 w p (![0,m,m+1,m+1+h]) rfl himages hrank'
  refine ⟨w,p,hpa,hpb,hpc,hpd,ha0,hb0,hc0,hh0,hQ,he1,huK,huH,hwH,hwKplus,hwKminus,himages,hG,?_,?_⟩
  · refine ⟨?_,x,n,σ,?_,?_,hm,hn,hσ,?_,?_,?_,?_,?_,?_,?_,by simp,by simp [hpd,h],hrank'⟩
    · constructor
      · exact_mod_cast (show (0:ℤ) < (p.a:ℤ) by rw [hpa]; exact ha0)
      constructor
      · exact_mod_cast (show (0:ℤ) < (p.b:ℤ) by rw [hpb]; exact hb0)
      constructor
      · exact_mod_cast (show (0:ℤ) < (p.c:ℤ) by rw [hpc]; exact hc0)
      · exact_mod_cast (show (0:ℤ) < (p.d:ℤ) by rw [hpd]; exact hd0)
    · simpa [hpd] using hx
    · simpa [hpd] using hxd
    · simpa [hpd] using hpa
    · simpa [hpc,hpd] using hpb
    · simpa [hpd,c,h] using hpc
    · simpa [hpd] using hQ
    · simpa only [he1,hpdR] using hAr
    · simpa [w,Q,hpd] using huK
    · simpa [w,h,hpd] using huH
  · intro S hS
    have hdetS : S.det = 0 := by
      by_contra hnS
      have he := Matrix.rank_of_det_ne_zero hnS
      rw [hS.2] at he
      norm_num at he
    have hsource : _root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.positiveSource S := by
      refine ⟨hS.1,?_⟩
      simpa [Matrix.det_fin_two,sub_eq_zero] using hdetS
    have hfactor := (_root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.result
      true [.advance,.exchange] [.advance] 1 1 1 0
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [_root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.wordMatrix,
        _root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.secondMatrix])
      (by norm_num)
      (by norm_num [_root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.wordMatrix,
        _root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.actionMatrix,
        GoldenCoding.GoldenModularStandardPair.goldenModularStep,
        HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
        Matrix.mul_apply,Fin.sum_univ_two])
      (by norm_num [_root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.wordMatrix,
        _root_.D5.S3.Observer.TraceFibers.FixedFiberPairModulus.actionMatrix,
        GoldenCoding.GoldenModularStandardPair.goldenModularStep,
        HyperbolicTransport.GoldenDualTimeRenormalization.goldenTimeReflectionMatrix,
        Matrix.mul_apply,Fin.sum_univ_two])).2.2.2.1
    obtain ⟨f,ℓ,hf,hℓ,hSf,htrace⟩ := hfactor S hsource
    have hf' : Positive f := ⟨hf 0,hf 1⟩
    refine ⟨f,ℓ,hf',⟨hℓ 0,hℓ 1⟩,hSf,fun u => (positive_sum u f hf').1,?_⟩
    intro k δ i
    rw [htrace]

#print axioms admitted_parameters_realize

end D5.S3.Observer.CubicGain.InteriorForwardRealization
