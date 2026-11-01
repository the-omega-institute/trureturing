/- GID: D5/S3/Observer/CubicGain/TerminalSourceRank
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/TerminalSourceRank
   mirror-E: none(waiver:universal-source-observation-rank)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Both actual fifth histories have full observation rank and fixed-source uniqueness. -/

import D5.S3.Observer.CubicGain.OriginalWorld
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Full ranks of the two literal six-reading observation maps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain.TerminalSourceRank
open D5.S3.Observer.CubicGain
open scoped Matrix

/-- The fifth action, after the common chronological prefix J,M,J,M. -/
inductive FifthAction | J | M
  deriving DecidableEq

def fifthActionMatrix : FifthAction → Mat
  | .J => actionJ
  | .M => actionM

/-- Each prefix uses the initial observation and every consecutive original clock. -/
def prefixProduct (F : FifthAction) (i : ℕ) : Mat :=
  ([actionJ,actionM,actionJ,actionM,fifthActionMatrix F].take i).foldl
    (fun Q E => E * Q) 1

def tau (F : FifthAction) (r b : ℝ) (i : ℕ) : ℝ :=
  Matrix.trace (prefixProduct F i * sourceMatrix r b)

def fifthTrace (F : FifthAction) (r b : ℝ) : ℝ :=
  match F with
  | .J => sourceN r b+r
  | .M => sourceN r b+(1+2*b)

def drift4 (r b : ℝ) : ℝ := (1+2*b)*parentLambda r b

def drift5 (F : FifthAction) (r b : ℝ) : ℝ :=
  1+fifthTrace F r b*(4-15/sourceJ r b+20/(1+b)-10/sourceN r b)

private def jNumerator (r b : ℝ) : ℝ :=
  let X := b^2+r-r^2
  let N := X+b*r
  let W := X+2*b*r
  b*(1+b)*X*N + W*(4*(b+6)*X*N-5*b*(1+b)*(3*N+2*X))

private def jObstruction (b : ℝ) : ℝ :=
  9*b^14-216*b^13-6960*b^12-14256*b^11+543416*b^10+
  4101632*b^9+13939808*b^8+29398144*b^7+42960384*b^6+
  44357120*b^5+31699968*b^4+15120384*b^3+4552704*b^2+778240*b+57344

set_option maxHeartbeats 2000000 in
-- The explicit polynomial coefficient expressions are checked in full.
private def jBezout4 (r b : ℝ) : ℝ :=
  - 30*b^13*r^5
  + 24*b^12*r^5
  + 13372*b^11*r^5
  + 171300*b^10*r^5
  + 896192*b^9*r^5
  + 2214576*b^8*r^5
  + 2692352*b^7*r^5
  + 3529728*b^6*r^5
  + 8198656*b^5*r^5
  + 12408832*b^4*r^5
  + 10003456*b^3*r^5
  + 4348928*b^2*r^5
  + 966656*b^1*r^5
  + 86016*r^5
  + 96*b^14*r^4
  + 534*b^13*r^4
  - 37108*b^12*r^4
  - 639512*b^11*r^4
  - 4366588*b^10*r^4
  - 15268624*b^9*r^4
  - 30868368*b^8*r^4
  - 44868096*b^7*r^4
  - 61280768*b^6*r^4
  - 77702656*b^5*r^4
  - 72934400*b^4*r^4
  - 44152832*b^3*r^4
  - 16032768*b^2*r^4
  - 3158016*b^1*r^4
  - 258048*r^4
  - 12*b^15*r^3
  - 1878*b^14*r^3
  - 15430*b^13*r^3
  + 275660*b^12*r^3
  + 4452324*b^11*r^3
  + 25540548*b^10*r^3
  + 77280432*b^9*r^3
  + 140562256*b^8*r^3
  + 177335168*b^7*r^3
  + 185778944*b^6*r^3
  + 172684288*b^5*r^3
  + 126638080*b^4*r^3
  + 63824896*b^3*r^3
  + 20057088*b^2*r^3
  + 3502080*b^1*r^3
  + 258048*r^3
  - 114*b^16*r^2
  + 492*b^15*r^2
  + 64584*b^14*r^2
  + 792570*b^13*r^2
  + 3672524*b^12*r^2
  + 4545920*b^11*r^2
  - 19303812*b^10*r^2
  - 85803568*b^9*r^2
  - 161334704*b^8*r^2
  - 194106624*b^7*r^2
  - 180252672*b^6*r^2
  - 139404800*b^5*r^2
  - 84319232*b^4*r^2
  - 35610624*b^3*r^2
  - 9468928*b^2*r^2
  - 1396736*b^1*r^2
  - 86016*r^2
  + 6*b^17*r^1
  + 1443*b^16*r^1
  + 4149*b^15*r^1
  - 327186*b^14*r^1
  - 3717332*b^13*r^1
  - 18175886*b^12*r^1
  - 47260804*b^11*r^1
  - 64474936*b^10*r^1
  - 33993040*b^9*r^1
  + 24221696*b^8*r^1
  + 58604288*b^7*r^1
  + 57040384*b^6*r^1
  + 38312960*b^5*r^1
  + 18566656*b^4*r^1
  + 5956608*b^3*r^1
  + 1095680*b^2*r^1
  + 86016*b^1*r^1
  + 18*b^18
  + 387*b^17
  - 9569*b^16
  - 251660*b^15
  - 1948184*b^14
  - 7191764*b^13
  - 13758064*b^12
  - 11105872*b^11
  + 6517504*b^10
  + 25942784*b^9
  + 32135424*b^8
  + 25283584*b^7
  + 13760512*b^6
  + 4895744*b^5
  + 995328*b^4
  + 86016*b^3

set_option maxHeartbeats 2000000 in
-- The explicit polynomial coefficient expressions are checked in full.
private def jBezout5 (r b : ℝ) : ℝ :=
  - 15*b^14*r^3
  - 18*b^13*r^3
  + 6830*b^12*r^3
  + 98206*b^11*r^3
  + 570804*b^10*r^3
  + 1609832*b^9*r^3
  + 2337872*b^8*r^3
  + 2936192*b^7*r^3
  + 5985792*b^6*r^3
  + 10143744*b^5*r^3
  + 10171904*b^4*r^3
  + 5974528*b^3*r^3
  + 2038784*b^2*r^3
  + 374784*b^1*r^3
  + 28672*r^3
  + 18*b^15*r^2
  + 312*b^14*r^2
  - 4762*b^13*r^2
  - 153454*b^12*r^2
  - 1435568*b^11*r^2
  - 6536928*b^10*r^2
  - 16991904*b^9*r^2
  - 28569632*b^8*r^2
  - 36262400*b^7*r^2
  - 40416256*b^6*r^2
  - 39214592*b^5*r^2
  - 28885504*b^4*r^2
  - 14405632*b^3*r^2
  - 4481024*b^2*r^2
  - 778240*b^1*r^2
  - 57344*r^2
  + 15*b^16*r^1
  - 357*b^15*r^1
  - 11633*b^14*r^1
  - 72904*b^13*r^1
  + 136060*b^12*r^1
  + 3317474*b^11*r^1
  + 15716036*b^10*r^1
  + 38058600*b^9*r^1
  + 57905168*b^8*r^1
  + 64146432*b^7*r^1
  + 57978624*b^6*r^1
  + 43660288*b^5*r^1
  + 25502720*b^4*r^1
  + 10534400*b^3*r^1
  + 2817024*b^2*r^1
  + 432128*b^1*r^1
  + 28672*r^1
  - 9*b^17
  - 189*b^16
  + 4699*b^15
  + 122692*b^14
  + 954176*b^13
  + 3570836*b^12
  + 6630556*b^11
  + 3335248*b^10
  - 11222224*b^9
  - 28720256*b^8
  - 35884032*b^7
  - 30128640*b^6
  - 18347008*b^5
  - 7977984*b^4
  - 2305024*b^3
  - 389120*b^2
  - 28672*b^1

set_option maxHeartbeats 2000000 in
-- Polynomial expansion checks the universal Bezout identity.
private theorem j_bezout (r b : ℝ) :
    jBezout4 r b*n4 r b+jBezout5 r b*jNumerator r b =
      2*b^8*(1+b)*jObstruction b := by
  unfold jBezout4 jBezout5 n4 jNumerator jObstruction
  ring

private theorem j_obstruction_pos (b : ℝ) (hb : 0 < b) (hb4 : b < 4) :
    0 < jObstruction b := by
  have hb2 : b^2 < 16 := by nlinarith
  have hb3 : b^3 < 64 := by
    calc b^3 = b^2*b := by ring
         _ < 16*b := mul_lt_mul_of_pos_right hb2 hb
         _ < 64 := by linarith
  have hp : 0 < 543416-14256*b-6960*b^2-216*b^3 := by nlinarith
  have hrest : 0 < 9*b^14+4101632*b^9+13939808*b^8+29398144*b^7+
      42960384*b^6+44357120*b^5+31699968*b^4+15120384*b^3+
      4552704*b^2+778240*b+57344 := by positivity
  have hid : jObstruction b = b^10*(543416-14256*b-6960*b^2-216*b^3)+
      (9*b^14+4101632*b^9+13939808*b^8+29398144*b^7+
      42960384*b^6+44357120*b^5+31699968*b^4+15120384*b^3+
      4552704*b^2+778240*b+57344) := by unfold jObstruction; ring
  rw [hid]
  exact add_pos (mul_pos (pow_pos hb _) hp) hrest

private theorem drift_nonzero (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b) :
    drift4 r b ≠ 0 ∨ drift5 F r b ≠ 0 := by
  have hu : 1+2*b ≠ 0 := ne_of_gt (by positivity : 0 < 1+2*b)
  cases F with
  | M =>
    rcases drift_vector_nonzero r b hr.le hr1.le hb with h | h
    · exact Or.inl (mul_ne_zero hu h)
    · right
      simpa [drift5,fifthTrace,fifthDrift,add_comm] using h
  | J =>
    by_cases hb4 : b < 4
    · by_contra h
      push Not at h
      obtain ⟨h4,h5⟩ := h
      have hl : parentLambda r b = 0 := (mul_eq_zero.mp h4).resolve_left hu
      have hn4 : n4 r b = 0 := by
        obtain ⟨hj,hn,ht,hu'⟩ := source_positivity r b hr.le hr1.le hb
        rw [n4_parentLambda r b (ne_of_gt hb) (ne_of_gt hj) (ne_of_gt hn)
          (ne_of_gt ht) (ne_of_gt hu'),hl,mul_zero]
      have hn5 : jNumerator r b = 0 := by
        have hid : jNumerator r b =
            b*(1+b)*(b^2+r-r^2)*(b^2+r-r^2+b*r)*drift5 .J r b := by
          obtain ⟨hj,hn,ht,_⟩ := source_positivity r b hr.le hr1.le hb
          unfold jNumerator drift5 fifthTrace
          field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht]
          unfold sourceN sourceJ
          field_simp [ne_of_gt hb]
          <;> ring
        rw [hid,h5,mul_zero]
      have hid := j_bezout r b
      rw [hn4,hn5,mul_zero,mul_zero,add_zero] at hid
      have hp : 0 < 2*b^8*(1+b)*jObstruction b :=
        mul_pos (by positivity) (j_obstruction_pos b hb hb4)
      linarith
    · exact Or.inl (mul_ne_zero hu (ne_of_gt
        (parentLambda_pos_of_four_le r b hr.le hr1.le hb (le_of_not_gt hb4))))

private theorem actual_traces (F : FifthAction) (r b : ℝ) :
    (fun i : Fin 6 => tau F r b i) =
      ![1,sourceJ r b,1+b,sourceN r b,1+2*b,fifthTrace F r b] := by
  ext i
  cases F <;> fin_cases i <;>
    norm_num [tau,prefixProduct,fifthActionMatrix,sourceMatrix,actionJ,actionM,
      Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two,sourceJ,sourceN,fifthTrace]
  all_goals ring

private theorem zero_readings (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b)
    (g : Polynomial ℝ) (hg : g.degree ≤ 3) (d : ℝ)
    (h : ∀ i : Fin 6, d+tau F r b i*g.eval (i : ℝ)=0) : d=0 ∧ g=0 := by
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
  let a : Gain := fun i => g.eval (i : ℝ)
  have hpoly : g=gainPoly a := polynomial_representation g hg
  have hrows (i : Fin 6) :
      d+(![1,sourceJ r b,1+b,sourceN r b,1+2*b,fifthTrace F r b] : Fin 6 → ℝ) i*
        gain a (i : ℕ)=0 := by
    have hi := h i
    rw [hpoly,gainPoly_eval] at hi
    simpa only [congrFun (actual_traces F r b) i] using hi
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  norm_num [gain] at h0 h1 h2 h3
  have ha : a = ![-d,-d/sourceJ r b,-d/(1+b),-d/sourceN r b] := by
    ext i
    fin_cases i <;> norm_num
    · linarith
    · apply (eq_div_iff (ne_of_gt hj)).mpr; nlinarith [h1]
    · apply (eq_div_iff (ne_of_gt ht)).mpr; nlinarith [h2]
    · apply (eq_div_iff (ne_of_gt hn)).mpr; nlinarith [h3]
  have h4 := hrows 4
  have h5 := hrows 5
  have he4 : d+(1+2*b)*gain a 4=drift4 r b*d := by
    rw [ha]
    norm_num [gain,drift4,parentLambda]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hu]
    <;> ring
  have he5 : d+fifthTrace F r b*gain a 5=drift5 F r b*d := by
    rw [ha]
    norm_num [gain,drift5]
    ring
  norm_num at h4 h5
  have hd : d=0 := by
    rcases drift_nonzero F r b hr hr1 hb with h4n | h5n
    · exact (mul_eq_zero.mp (he4.symm.trans h4)).resolve_left h4n
    · exact (mul_eq_zero.mp (he5.symm.trans h5)).resolve_left h5n
  refine ⟨hd,?_⟩
  rw [hpoly,ha,hd]
  norm_num [gainPoly]

/-- Ordinary coefficient order is (d,g₀,g₁,g₂,g₃). -/
def observation (F : FifthAction) (r b : ℝ) : Matrix (Fin 6) (Fin 5) ℝ :=
  fun i => ![1,tau F r b i,(i : ℝ)*tau F r b i,
    (i : ℝ)^2*tau F r b i,(i : ℝ)^3*tau F r b i]

/-- Rows one through five after substituting the initial equation d=-g₀. -/
def reducedObservation (F : FifthAction) (r b : ℝ) : Matrix (Fin 5) (Fin 4) ℝ :=
  fun i => ![tau F r b i.succ-1,(i.succ : ℝ)*tau F r b i.succ,
    (i.succ : ℝ)^2*tau F r b i.succ,(i.succ : ℝ)^3*tau F r b i.succ]

def residualColumn (F : FifthAction) (r b : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  fun i _ => (![drift4 r b,drift5 F r b] : Fin 2 → ℝ) i

private theorem observation_kernel (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b)
    (v : Fin 5 → ℝ) (hv : observation F r b *ᵥ v=0) : v=0 := by
  let c : Gain := fun i => v i.succ
  let g := Polynomial.ofFn 4 c
  have hrows (i : Fin 6) : v 0+tau F r b i*g.eval (i : ℝ)=0 := by
    have hi := congrFun hv i
    simpa [observation,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_four,
      g,c,Polynomial.ofFn_eq_sum_monomial,pow_succ,mul_comm,mul_left_comm,mul_assoc,
      add_comm,add_left_comm,add_assoc,mul_add,add_mul] using hi
  obtain ⟨hd,hg⟩ := zero_readings F r b hr hr1 hb g (coefficient_degree c) (v 0) hrows
  have hc : c=0 := Polynomial.injective_ofFn 4 (by simpa [g] using hg)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hd
  · exact congrFun hc j

private theorem observation_injective (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b) :
    Function.Injective (observation F r b).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  exact observation_kernel F r b hr hr1 hb

private theorem reduced_injective (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b) :
    Function.Injective (reducedObservation F r b).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro c hc
  let v : Fin 5 → ℝ := ![-c 0,c 0,c 1,c 2,c 3]
  have hv : observation F r b *ᵥ v=0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have ht0 : tau F r b 0=1 := by
        simpa using congrFun (actual_traces F r b) 0
      simp [observation,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_four,v,ht0]
    · have hj := congrFun hc j
      simp [observation,reducedObservation,Matrix.mulVec,dotProduct,
        Fin.sum_univ_four,Fin.sum_univ_succ,Fin.sum_univ_four,v] at hj ⊢
      linear_combination hj
  have hzero := observation_kernel F r b hr hr1 hb v hv
  ext i
  fin_cases i
  · exact congrFun hzero 1
  · exact congrFun hzero 2
  · exact congrFun hzero 3
  · exact congrFun hzero 4

private theorem residual_injective (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b) :
    Function.Injective (residualColumn F r b).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [residualColumn,Matrix.mulVec,dotProduct] at h0 h1
  have hz : v 0=0 := by
    rcases drift_nonzero F r b hr hr1 hb with h | h
    · exact h0.resolve_left h
    · exact h1.resolve_left h
  ext i
  fin_cases i
  exact hz

/-- This readout uses one unchanged ordinary-coefficient polynomial and drift. -/
def actualRead (F : FifthAction) (W : OriginalWorld) (i : ℕ) : ℝ :=
  W.2.2.1+tau F W.1 W.2.1 i*(originalPolynomial W).eval (i : ℝ)

/-- The complete literal H₅ fibre, with all four response parameters arbitrary. -/
def Compatible (F : FifthAction) (C z Y p : ℝ) (W : OriginalWorld) : Prop :=
  0 < W.1 ∧ W.1 < 1 ∧ 0 < W.2.1 ∧ originalPolynomial W ≠ 0 ∧
    ∀ i : Fin 6, actualRead F W i=(![0,24,C,z,Y,p] : Fin 6 → ℝ) i

private theorem fixed_source_unique (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b)
    (W V : OriginalWorld) (hWr : W.1=r) (hWb : W.2.1=b)
    (hVr : V.1=r) (hVb : V.2.1=b)
    (h : ∀ i : Fin 6, actualRead F W i=actualRead F V i) : W=V := by
  let g := originalPolynomial W-originalPolynomial V
  have hg : g.degree ≤ 3 :=
    (Polynomial.degree_sub_le _ _).trans (max_le
      (coefficient_degree W.2.2.2) (coefficient_degree V.2.2.2))
  have hrows (i : Fin 6) :
      (W.2.2.1-V.2.2.1)+tau F r b i*g.eval (i : ℝ)=0 := by
    have hi := h i
    simp only [actualRead,hWr,hWb,hVr,hVb] at hi
    simp only [g,Polynomial.eval_sub]
    linear_combination hi
  obtain ⟨hd,hgzero⟩ := zero_readings F r b hr hr1 hb g hg _ hrows
  have hcoeff : W.2.2.2=V.2.2.2 :=
    Polynomial.injective_ofFn 4 (sub_eq_zero.mp hgzero)
  exact Prod.ext (hWr.trans hVr.symm)
    (Prod.ext (hWb.trans hVb.symm) (Prod.ext (sub_eq_zero.mp hd) hcoeff))

/-- Both actual fifth prefixes have full observation ranks on every strict source;
the complete fibre has at most one world over each fixed source. -/
theorem observation_ranks_and_fixed_source_uniqueness (F : FifthAction) (r b : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hb : 0 < b) :
    (observation F r b).rank=5 ∧ (reducedObservation F r b).rank=4 ∧
    (residualColumn F r b).rank=1 ∧
    ∀ C z Y p : ℝ,
      Set.Subsingleton {W : OriginalWorld | Compatible F C z Y p W ∧ W.1=r ∧ W.2.1=b} := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Matrix.rank,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      LinearMap.finrank_range_of_inj (observation_injective F r b hr hr1 hb)
  · simpa only [Matrix.rank,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      LinearMap.finrank_range_of_inj (reduced_injective F r b hr hr1 hb)
  · simpa only [Matrix.rank,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      LinearMap.finrank_range_of_inj (residual_injective F r b hr hr1 hb)
  · intro C z Y p W hW V hV
    exact fixed_source_unique F r b hr hr1 hb W V hW.2.1 hW.2.2 hV.2.1 hV.2.2
      (fun i => (hW.1.2.2.2.2 i).trans (hV.1.2.2.2.2 i).symm)

#print axioms observation_ranks_and_fixed_source_uniqueness
end D5.S3.Observer.CubicGain.TerminalSourceRank
