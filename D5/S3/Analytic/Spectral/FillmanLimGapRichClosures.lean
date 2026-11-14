/- GID: D5/S3/Analytic/Spectral/FillmanLimGapRichClosures
   generality: G
   mirror-B: D5/B/S3/Analytic/Spectral/FillmanLimGapRichClosures
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Gap-rich alphabets fail closure under union, sum, and ordered product. -/

/-
admission_basis: open-problem-resolution (#29166; Refuted)
escape_witness: none (settling result)
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30475
Direct frozen dependencies (declaration identities):
F1: D5/S0/Observation/MatrixTracePowerSum.pow_add_two @ sha256:477f52a1cada3768c6c6695f7bf1e92216cc53ac6f22ad3f67270f1f31f452be
F2: D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two @ sha256:c3a059dba6dacff2daf43a6483f3e2bb7036930561a43d038fdbb8225d03adff
F3: D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.PlaneGenerator @ sha256:415da39038d174df12afbf807a8d677f347f7becccf7d156a97568b8f513a073
F4: D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.ellipticGenerator @ sha256:91ca12da68963997c61ce1ebfa3c2dac6bd0fb671ea68dc2f4b5a8ae4ae071ce
F5: D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.elliptic_generator_square @ sha256:ee07986793fea1bd7999ed621aa669ae4536a5b38c79cb8ac8d5d1f1009915db
Per-declaration classification; definitions specify objects rather than theorem assertions.
Consumed bind-only helpers organize proofs and supply no independent escape witness.
claim: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: result
lBlock: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: l_distance_sq,l_gap_rich,l_lipschitz,l_relative_trace,l_transfer_resonance,result,sumCenter,sum_center_member,sum_near_resonance,sum_not_gap_rich,sum_transfer_resonance
uBlock: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: cancellation_resonance,productCenter,product_center_member,product_near_resonance,product_not_gap_rich,result,u_distance_sq,u_gap_rich,u_lipschitz,u_relative_trace,u_transfer_resonance,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound
vBlock: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: cancellation_resonance,productCenter,product_center_member,product_near_resonance,product_not_gap_rich,result,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound,v_distance_sq,v_gap_rich,v_lipschitz,v_relative_trace,v_transfer_resonance
j_square: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F3,F4,F5; consumers: neg_j_trace_bound
transfer_det: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: block_transfer_determinant,cancellation_resonance,l_gap_rich,u_gap_rich,union_word_bound,v_gap_rich
l_transfer_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: l_gap_rich
u_transfer_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: cancellation_resonance,u_gap_rich,union_near_u_resonance
v_transfer_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: cancellation_resonance,union_near_v_resonance,v_gap_rich
l_relative_trace: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: l_gap_rich
u_relative_trace: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: u_gap_rich
v_relative_trace: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: v_gap_rich
sum_transfer_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: sum_near_resonance
cancellation_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_near_resonance
fold_determinant: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: block_transfer_determinant,gap_rich_components
fold_constant: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components,product_not_gap_rich,sum_not_gap_rich
relative_prefix_suffix: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components
interval_perturb: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components
componentAlphabet: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: gap_rich_components,l_gap_rich,product_center_member,product_near_resonance,product_not_gap_rich,result,sum_center_member,sum_near_resonance,sum_not_gap_rich,u_gap_rich,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound,v_gap_rich
gap_rich_components: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1,F2; consumers: l_gap_rich,u_gap_rich,v_gap_rich
block_transfer_determinant: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: l_gap_rich,u_gap_rich,v_gap_rich
l_distance_sq: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: l_lipschitz
u_distance_sq: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: u_lipschitz
v_distance_sq: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: v_lipschitz
l_lipschitz: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: l_gap_rich
u_lipschitz: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: u_gap_rich
v_lipschitz: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: v_gap_rich
l_gap_rich: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1,F2; consumers: result
u_gap_rich: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1,F2; consumers: result
v_gap_rich: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1,F2; consumers: result
qSeq: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: not_discrete_scaled_resonances,productCenter,product_center_member,product_near_resonance,product_not_gap_rich,q_bounds,q_subsequence,q_zero,result,sumCenter,sum_center_member,sum_near_resonance,sum_not_gap_rich,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound
rSeq: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: hi,interval_nonempty,isolate_component,isolate_sum_components,lo,mid,midpoint_member,product_near_resonance,product_not_gap_rich,radius_le_one,radius_positive,radius_separation,sum_near_resonance,sum_not_gap_rich,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound
lo: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: interval_nonempty,isolate_component,isolate_sum_components,midpoint_member,product_center_member,product_near_resonance,product_not_gap_rich,result,sum_center_member,sum_near_resonance,sum_not_gap_rich,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound
hi: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: interval_nonempty,isolate_component,isolate_sum_components,midpoint_member,product_center_member,product_near_resonance,product_not_gap_rich,result,sum_center_member,sum_near_resonance,sum_not_gap_rich,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound
mid: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: isolate_sum_components,midpoint_member,productCenter,product_center_member,product_near_resonance,sumCenter,sum_center_member,sum_near_resonance,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich,union_word_bound
radius_positive: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: interval_nonempty,isolate_component,isolate_sum_components,midpoint_member,product_not_gap_rich,sum_not_gap_rich,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich
radius_le_one: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: union_near_u_resonance,union_near_v_resonance
radius_separation: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: isolate_component,isolate_sum_components
interval_nonempty: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: result
midpoint_member: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_center_member,product_near_resonance,sum_center_member,union_near_u_resonance,union_near_v_resonance,union_not_gap_rich
q_bounds: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: union_near_u_resonance,union_near_v_resonance
q_zero: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: not_discrete_scaled_resonances
q_subsequence: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: not_discrete_scaled_resonances
not_discrete_scaled_resonances: proof_shape: content; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich,sum_not_gap_rich,union_not_gap_rich
isolate_component: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_near_resonance,union_near_u_resonance,union_near_v_resonance
isolate_sum_components: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: sum_near_resonance
singleWord: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich,single_word_close,sum_not_gap_rich
pairWord: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: pair_word_periodic,union_not_gap_rich,union_word_bound
orderedPair: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: block_transfer_append,productCenter,product_near_resonance
block_transfer_append: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_near_resonance
neg_identity_trace_bound: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich,union_word_bound
neg_j_trace_bound: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F3,F4,F5; consumers: sum_not_gap_rich
single_word_close: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich,sum_not_gap_rich
pair_word_periodic: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: union_word_bound
not_gap_rich_of_obstructions: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich,sum_not_gap_rich,union_not_gap_rich
sumCenter: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: sum_center_member,sum_near_resonance,sum_not_gap_rich
productCenter: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_center_member,product_near_resonance,product_not_gap_rich
sum_center_member: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: sum_not_gap_rich
sum_near_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: sum_not_gap_rich
sum_not_gap_rich: proof_shape: content; escape_witness: none; Direct frozen dependencies: F3,F4,F5; consumers: result
product_center_member: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich
product_near_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: product_not_gap_rich
product_not_gap_rich: proof_shape: content; escape_witness: none; Direct frozen dependencies: none; consumers: result
union_near_u_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: union_word_bound
union_near_v_resonance: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: union_word_bound
alternating_list: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: alternating_even_fold
pairs_fold: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: alternating_even_fold
alternating_even_fold: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: union_word_bound
union_word_bound: proof_shape: content; escape_witness: none; Direct frozen dependencies: none; consumers: union_not_gap_rich
union_not_gap_rich: proof_shape: content; escape_witness: none; Direct frozen dependencies: none; consumers: result
result: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1,F2,F3,F4,F5; consumers: terminal result
utility: none; the payload uses infinite alphabets, arbitrary positive word lengths,
and an unrestricted positive-semigroup criterion, rather than a finite checker.
-/

import D5.S3.Analytic.Spectral.FillmanLimPositiveSemigroup
import D5.S3.Analytic.Spectral.FillmanLimGapRichWords
import D5.S3.Analytic.ReflectedSpectrum.EllipticHyperbolicReflectionTrichotomy

namespace D5.S3.Analytic.Spectral.FillmanLimGapRichClosures

noncomputable section
open Set
open scoped Topology Pointwise
open D5.S3.Analytic.Spectral.FillmanLimGapRichWords
def claim : Prop :=
  (∀ k : ℕ, 0 < k → ∀ X₁ X₂ : Set ((EuclideanSpace ℝ (Fin k))),
    GapRich X₁ → GapRich X₂ → GapRich (X₁ ∪ X₂)) ∨
  (∀ k : ℕ, 0 < k → ∀ X₁ X₂ : Set ((EuclideanSpace ℝ (Fin k))),
    GapRich X₁ → GapRich X₂ → GapRich (X₁ + X₂)) ∨
  (∀ k ℓ : ℕ, 0 < k → 0 < ℓ → ∀ X₁ : Set ((EuclideanSpace ℝ (Fin k))), ∀ X₃ : Set ((EuclideanSpace ℝ (Fin ℓ))),
    GapRich X₁ → GapRich X₃ → GapRich (cartesianProduct X₁ X₃))

private def lBlock (h q t : ℝ) : (EuclideanSpace ℝ (Fin 3)) :=
  WithLp.toLp 2 ![t, q, 2*q-h-t]
private def uBlock (h q t : ℝ) : (EuclideanSpace ℝ (Fin 5)) :=
  WithLp.toLp 2 ![t, q, 2*q-h-t, q, q]
private def vBlock (h q t : ℝ) : (EuclideanSpace ℝ (Fin 5)) :=
  WithLp.toLp 2 ![q, t, q, 2*q+h-t, q]

private theorem j_square : transfer 0 0 * transfer 0 0 = -(1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := D5.S3.Analytic.ReflectedSpectrum.EllipticHyperbolicReflectionTrichotomy.elliptic_generator_square 1
  convert h using 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [transfer, D5.S3.Analytic.ReflectedSpectrum.EllipticHyperbolicReflectionTrichotomy.ellipticGenerator]

private theorem transfer_det (x E : ℝ) : Matrix.det (transfer x E) = 1 := by
  simp [transfer, Matrix.det_fin_two]

private theorem l_transfer_resonance (h q t : ℝ) :
    blockTransfer (lBlock h q t) q = -(transfer 0 h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockTransfer, lBlock, List.ofFn_succ, transfer, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem u_transfer_resonance (h q t : ℝ) :
    blockTransfer (uBlock h q t) q = transfer 0 h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockTransfer, uBlock, List.ofFn_succ, transfer, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem v_transfer_resonance (h q t : ℝ) :
    blockTransfer (vBlock h q t) q = -(Matrix.adjugate (transfer 0 h)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockTransfer, vBlock, List.ofFn_succ, transfer, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring

private theorem l_relative_trace (h q t s E : ℝ) :
    Matrix.trace (blockTransfer (lBlock h q t) E *
      Matrix.adjugate (blockTransfer (lBlock h q s) E)) =
        2 + (E-q)^2*(t-s)^2 := by
  simp [blockTransfer, lBlock, List.ofFn_succ, transfer, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

private theorem u_relative_trace (h q t s E : ℝ) :
    Matrix.trace (blockTransfer (uBlock h q t) E *
      Matrix.adjugate (blockTransfer (uBlock h q s) E)) =
        2 + (E-q)^2*(t-s)^2 := by
  simp [blockTransfer, uBlock, List.ofFn_succ, transfer, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

private theorem v_relative_trace (h q t s E : ℝ) :
    Matrix.trace (blockTransfer (vBlock h q t) E *
      Matrix.adjugate (blockTransfer (vBlock h q s) E)) =
        2 + (E-q)^2*(t-s)^2 := by
  simp [blockTransfer, vBlock, List.ofFn_succ, transfer, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

private theorem sum_transfer_resonance (h q t s : ℝ) :
    blockTransfer (lBlock h q t + lBlock (-h) q s) (2*q) = -(transfer 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockTransfer, lBlock, List.ofFn_succ, transfer, Matrix.mul_apply,
      Fin.sum_univ_two, PiLp.add_apply] <;> ring_nf <;> simp

private theorem cancellation_resonance (h q t s : ℝ) :
    blockTransfer (vBlock h q s) q * blockTransfer (uBlock h q t) q = -(1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [v_transfer_resonance, u_transfer_resonance, neg_mul,
    Matrix.adjugate_mul, transfer_det, one_smul]

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem fold_determinant {Y : Type} (f : Y → (Matrix (Fin 2) (Fin 2) ℝ)) (l : List Y)
    (hl : ∀ a ∈ l, Matrix.det (f a)=1) (M : (Matrix (Fin 2) (Fin 2) ℝ)) (hM : Matrix.det M=1) :
    Matrix.det (l.foldl (fun B a => f a*B) M)=1 := by
  induction l generalizing M with
  | nil => exact hM
  | cons a l ih =>
    apply ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    rw [Matrix.det_mul,hl a (by simp),hM,mul_one]

private theorem fold_constant {Y : Type} (f : Y → (Matrix (Fin 2) (Fin 2) ℝ)) (l : List Y) (M : (Matrix (Fin 2) (Fin 2) ℝ))
    (hl : ∀ a ∈ l, f a=M) : l.foldl (fun B a => f a*B) 1=M^l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons,List.length_cons]
    rw [foldLeftStart,ih (fun b hb => hl b (List.mem_cons_of_mem a hb)),
      hl a (by simp),mul_one,pow_succ]

private theorem relative_prefix_suffix (P Q A B : (Matrix (Fin 2) (Fin 2) ℝ))
    (hP : Matrix.det P=1) (hQ : Matrix.det Q=1) :
    Matrix.trace ((Q*A*P)*Matrix.adjugate (Q*B*P)) =
      Matrix.trace (A*Matrix.adjugate B) := by
  have hPP : P*Matrix.adjugate P=1 := by rw [Matrix.mul_adjugate,hP,one_smul]
  have hQQ : Matrix.adjugate Q*Q=1 := by rw [Matrix.adjugate_mul,hQ,one_smul]
  calc
    _ = Matrix.trace (Q*(A*(P*Matrix.adjugate P)*Matrix.adjugate B)*Matrix.adjugate Q) := by
      simp only [Matrix.adjugate_mul_distrib,mul_assoc]
    _ = Matrix.trace (Q*(A*Matrix.adjugate B)*Matrix.adjugate Q) := by rw [hPP,mul_one]
    _ = Matrix.trace ((Matrix.adjugate Q*Q)*(A*Matrix.adjugate B)) := by
      rw [Matrix.trace_mul_cycle,← mul_assoc]
    _ = Matrix.trace (A*Matrix.adjugate B) := by rw [hQQ,one_mul]

private theorem interval_perturb (a b t ε : ℝ) (hab : a<b) (ht : t ∈ Set.Icc a b)
    (hε : 0<ε) : ∃ s ∈ Set.Icc a b, t≠s ∧ |t-s|<ε := by
  by_cases htb : t<b
  · obtain ⟨s,hts,hs⟩ := exists_between (lt_min htb (by linarith : t<t+ε))
    refine ⟨s,⟨by linarith [ht.1],le_trans hs.le (min_le_left _ _)⟩,ne_of_lt hts,?_⟩
    rw [abs_of_neg (by linarith)]
    linarith [lt_of_lt_of_le hs (min_le_right b (t+ε))]
  · have hbt : t=b := le_antisymm ht.2 (le_of_not_gt htb)
    obtain ⟨s,hs,hst⟩ := exists_between (max_lt (by linarith : a<t) (by linarith : t-ε<t))
    refine ⟨s,⟨le_trans (le_max_left _ _) hs.le,by linarith [ht.2]⟩,ne_of_gt hst,?_⟩
    rw [abs_of_pos (by linarith)]
    linarith [lt_of_le_of_lt (le_max_right a (t-ε)) hs]

private def componentAlphabet {k : ℕ} (F : ℝ → ℝ → (EuclideanSpace ℝ (Fin k)))
    (q a b : ℕ → ℝ) : Set ((EuclideanSpace ℝ (Fin k))) :=
  {z | ∃ n : ℕ, ∃ t : ℝ, t ∈ Set.Icc (a n) (b n) ∧ z=F (q n) t}

private theorem gap_rich_components {k : ℕ} (F : ℝ → ℝ → (EuclideanSpace ℝ (Fin k)))
    (q a b : ℕ → ℝ) (hab : ∀ n,a n<b n)
    (hdet : ∀ q t E,Matrix.det (blockTransfer (F q t) E)=1)
    (hrel : ∀ q t s E,Matrix.trace (blockTransfer (F q t) E*
      Matrix.adjugate (blockTransfer (F q s) E))=2+(E-q)^2*(t-s)^2)
    (hlip : ∀ q t s,dist (F q t) (F q s) ≤ 2*|t-s|)
    (R : (Matrix (Fin 2) (Fin 2) ℝ)) (hRdet : Matrix.det R=1) (hRhyp : 2 < |Matrix.trace R|)
    (hres : ∀ q t,blockTransfer (F q t) q=R) :
    GapRichWithExceptionalSet (componentAlphabet F q a b) ∅ := by
  refine ⟨Set.subsingleton_empty.isDiscrete,?_⟩
  intro E hE x hx ε hε
  have hreps : ∀ i : Fin (x.length : ℕ),
      ∃ n : ℕ, ∃ t : ℝ, t ∈ Set.Icc (a n) (b n) ∧ x.letter i=F (q n) t := hx
  choose ni ti hti hi using hreps
  have hxlist : ∀ z ∈ List.ofFn x.letter,z ∈ componentAlphabet F q a b :=
    List.forall_mem_ofFn_iff.mpr hx
  have hdetX (z : (EuclideanSpace ℝ (Fin k))) (hz : z ∈ componentAlphabet F q a b) :
      Matrix.det (blockTransfer z E)=1 := by
    obtain ⟨n,t,ht,rfl⟩ := hz
    exact hdet _ _ _
  have hxdet : Matrix.det (extend blockTransfer x E)=1 :=
    fold_determinant _ _ (fun z hz => hdetX z (hxlist z hz)) 1 (Matrix.det_one)
  by_cases hall : ∀ i : Fin (x.length : ℕ),E=q (ni i)
  · have hconst : ∀ z ∈ List.ofFn x.letter,blockTransfer z E=R := by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      rw [hi i,hall i,hres]
    refine ⟨x,hx,goodDistance x x ε (goodSelf x ε hε),?_⟩
    unfold extend
    rw [fold_constant _ _ R hconst,List.length_ofFn]
    exact D5.S3.Analytic.Spectral.FillmanLimPositiveSemigroup.hyperbolicTracePower R hRdet hRhyp _ x.length.pos
  · obtain ⟨i,hiE⟩ := not_forall.mp hall
    obtain ⟨s,hs,hts,hdist⟩ := interval_perturb (a (ni i)) (b (ni i)) (ti i) (ε/2)
      (hab _) (hti i) (by linarith)
    have hpert : dist (x.letter i) (F (q (ni i)) s)<ε := by
      rw [hi i]
      exact lt_of_le_of_lt (hlip _ _ _) (by linarith)
    obtain ⟨pre,post,hsplit⟩ := List.mem_iff_append.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
    let l : List ((EuclideanSpace ℝ (Fin k))) := pre++F (q (ni i)) s::post
    have hl : 0<l.length := by simp [l]
    let y := wordOfList l hl
    have hylist : ∀ z ∈ l,z ∈ componentAlphabet F q a b := by
      intro z hz
      simp only [l,List.mem_append,List.mem_cons] at hz
      rcases hz with hz | rfl | hz
      · exact hxlist z (by rw [hsplit];exact List.mem_append.mpr (Or.inl hz))
      · exact ⟨ni i,s,hs,rfl⟩
      · exact hxlist z (by rw [hsplit];simp only [List.mem_append,List.mem_cons];tauto)
    have hyX : WordOver (componentAlphabet F q a b) y := by
      have hh : ∀ z ∈ List.ofFn y.letter,z ∈ componentAlphabet F q a b := by
        rw [show List.ofFn y.letter=l from wordOfListLetters l hl]
        exact hylist
      exact List.forall_mem_ofFn_iff.mp hh
    have hrefl (l : List ((EuclideanSpace ℝ (Fin k)))) :
        List.Forall₂ (fun a b => dist a b<ε) l l :=
      List.forall₂_same.mpr (fun z hz => by simpa using hε)
    have hgood : Good x ε y := by
      apply goodOfForallTwo
      rw [hsplit,show List.ofFn y.letter=l from wordOfListLetters l hl]
      exact List.rel_append (hrefl pre) (List.Forall₂.cons hpert (hrefl post))
    let P : (Matrix (Fin 2) (Fin 2) ℝ) := pre.foldl (fun B z => blockTransfer z E*B) 1
    let Q : (Matrix (Fin 2) (Fin 2) ℝ) := post.foldl (fun B z => blockTransfer z E*B) 1
    have hP : Matrix.det P=1 := by
      apply fold_determinant _ _ _ 1 Matrix.det_one
      intro z hz
      exact hdetX z (hxlist z (by rw [hsplit];exact List.mem_append.mpr (Or.inl hz)))
    have hQ : Matrix.det Q=1 := by
      apply fold_determinant _ _ _ 1 Matrix.det_one
      intro z hz
      apply hdetX z
      apply hxlist z
      rw [hsplit]
      simp only [List.mem_append,List.mem_cons]
      tauto
    have hxT : extend blockTransfer x E=Q*blockTransfer (x.letter i) E*P := by
      unfold extend
      rw [hsplit,List.foldl_append,List.foldl_cons,foldLeftStart]
      simp only [P,Q,mul_assoc]
    have hyT : extend blockTransfer y E=Q*blockTransfer (F (q (ni i)) s) E*P := by
      unfold extend
      rw [show List.ofFn y.letter=l from wordOfListLetters l hl]
      simp only [l,List.foldl_append,List.foldl_cons]
      rw [foldLeftStart]
      simp only [P,Q,mul_assoc]
    have hrelXY : 2 < |Matrix.trace (extend blockTransfer x E*
        Matrix.adjugate (extend blockTransfer y E))| := by
      rw [hxT,hyT,relative_prefix_suffix P Q _ _ hP hQ,hi i,hrel]
      have hpos : 0<(E-q (ni i))^2*(ti i-s)^2 :=
        mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hiE)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hts))
      exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    have hydet : Matrix.det (extend blockTransfer y E)=1 := by
      unfold extend
      rw [show List.ofFn y.letter=l from wordOfListLetters l hl]
      exact fold_determinant _ _ (fun z hz => hdetX z (hylist z hz)) 1 Matrix.det_one
    obtain ⟨C,hC,hChyp⟩ := D5.S3.Analytic.Spectral.FillmanLimPositiveSemigroup.positiveRelativeCriterion
      (extend blockTransfer x E) (extend blockTransfer y E) hxdet hydet hrelXY
    rcases closureWordRealization (componentAlphabet F q a b) blockTransfer x y E ε
      (goodSelf x ε hε) hgood hx hyX C hC with rfl | ⟨z,hzX,hz,hzC⟩
    · norm_num [Matrix.trace_fin_two] at hChyp
    · exact ⟨z,hzX,goodDistance x z ε hz,hzC ▸ hChyp⟩

set_option maxHeartbeats 800000
private theorem block_transfer_determinant {k : ℕ} (x : (EuclideanSpace ℝ (Fin k))) (E : ℝ) :
    Matrix.det (blockTransfer x E)=1 :=
  fold_determinant (fun a => transfer a E) _ (fun a ha => transfer_det a E) 1 Matrix.det_one

private theorem l_distance_sq (h q t s : ℝ) :
    dist (lBlock h q t) (lBlock h q s)^2=2*(t-s)^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [lBlock,Fin.sum_univ_succ,Real.dist_eq,sq_abs]
  ring

private theorem u_distance_sq (h q t s : ℝ) :
    dist (uBlock h q t) (uBlock h q s)^2=2*(t-s)^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [uBlock,Fin.sum_univ_succ,Real.dist_eq,sq_abs]
  ring

private theorem v_distance_sq (h q t s : ℝ) :
    dist (vBlock h q t) (vBlock h q s)^2=2*(t-s)^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [vBlock,Fin.sum_univ_succ,Real.dist_eq,sq_abs]
  ring

private theorem l_lipschitz (h q t s : ℝ) :
    dist (lBlock h q t) (lBlock h q s) ≤ 2*|t-s| := by
  have hd := l_distance_sq h q t s
  nlinarith [sq_abs (t-s),dist_nonneg (x := lBlock h q t) (y := lBlock h q s),abs_nonneg (t-s)]

private theorem u_lipschitz (h q t s : ℝ) :
    dist (uBlock h q t) (uBlock h q s) ≤ 2*|t-s| := by
  have hd := u_distance_sq h q t s
  nlinarith [sq_abs (t-s),dist_nonneg (x := uBlock h q t) (y := uBlock h q s),abs_nonneg (t-s)]

private theorem v_lipschitz (h q t s : ℝ) :
    dist (vBlock h q t) (vBlock h q s) ≤ 2*|t-s| := by
  have hd := v_distance_sq h q t s
  nlinarith [sq_abs (t-s),dist_nonneg (x := vBlock h q t) (y := vBlock h q s),abs_nonneg (t-s)]

private theorem l_gap_rich (h : ℝ) (hh : 2 < |h|) (q a b : ℕ → ℝ) (hab : ∀ n,a n<b n) :
    GapRich (componentAlphabet (lBlock h) q a b) := by
  refine ⟨∅,gap_rich_components (lBlock h) q a b hab
    (fun q t E => block_transfer_determinant _ _) (l_relative_trace h) (l_lipschitz h)
    (-(transfer 0 h)) ?_ ?_ (l_transfer_resonance h)⟩
  · simp [Matrix.det_neg,transfer_det]
  · simpa [Matrix.trace_fin_two,transfer] using hh

private theorem u_gap_rich (h : ℝ) (hh : 2 < |h|) (q a b : ℕ → ℝ) (hab : ∀ n,a n<b n) :
    GapRich (componentAlphabet (uBlock h) q a b) := by
  refine ⟨∅,gap_rich_components (uBlock h) q a b hab
    (fun q t E => block_transfer_determinant _ _) (u_relative_trace h) (u_lipschitz h)
    (transfer 0 h) (transfer_det 0 h) ?_ (u_transfer_resonance h)⟩
  simpa [Matrix.trace_fin_two,transfer] using hh

private theorem v_gap_rich (h : ℝ) (hh : 2 < |h|) (q a b : ℕ → ℝ) (hab : ∀ n,a n<b n) :
    GapRich (componentAlphabet (vBlock h) q a b) := by
  refine ⟨∅,gap_rich_components (vBlock h) q a b hab
    (fun q t E => block_transfer_determinant _ _) (v_relative_trace h) (v_lipschitz h)
    (-(Matrix.adjugate (transfer 0 h))) ?_ ?_ (v_transfer_resonance h)⟩
  · simp [Matrix.det_neg,Matrix.det_adjugate,transfer_det]
  · simpa [Matrix.trace_fin_two,transfer,Matrix.adjugate_fin_two] using hh

open Filter Set
open scoped Topology
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def qSeq (n : ℕ) : ℝ :=
  (2*((n+1-2^(Nat.log 2 (n+1)) : ℕ) : ℝ)+1)/(2 : ℝ)^(Nat.log 2 (n+1)+1)
private def rSeq (n : ℕ) : ℝ := (1/3 : ℝ)^(n+1)
private def lo (n : ℕ) : ℝ := 10+rSeq n
private def hi (n : ℕ) : ℝ := 10+(11/10)*rSeq n
private def mid (n : ℕ) : ℝ := 10+(21/20)*rSeq n

private theorem radius_positive (n : ℕ) : 0<rSeq n := by dsimp [rSeq]; positivity
private theorem radius_le_one (n : ℕ) : rSeq n≤1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem radius_separation {m n : ℕ} (h : m<n) : 3*rSeq n≤rSeq m := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show m+1≤n by omega)
  rw [hd]
  unfold rSeq
  rw [show m+1+d+1=(m+1)+(d+1) by omega,pow_add,pow_succ]
  have hp : (1/3 : ℝ)^d≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hh := mul_le_of_le_one_right (by positivity : 0≤(1/3 : ℝ)^(m+1)) hp
  simp only [pow_succ] at hh ⊢
  nlinarith

private theorem interval_nonempty (n : ℕ) : lo n<hi n := by
  have h := radius_positive n
  dsimp [lo,hi]
  linarith

private theorem midpoint_member (n : ℕ) : mid n ∈ Set.Icc (lo n) (hi n) := by
  have h := radius_positive n
  dsimp [mid,lo,hi]
  constructor <;> linarith

private theorem q_bounds (n : ℕ) : 0≤qSeq n ∧ qSeq n≤1 := by
  let m := Nat.log 2 (n+1)
  have hlow : 2^m≤n+1 := Nat.pow_log_le_self 2 (by omega)
  have hupp : n+1<2^(m+1) := Nat.lt_pow_succ_log_self (by decide) (n+1)
  have hj : 2*(n+1-2^m)+1<2^(m+1) := by rw [pow_succ] at *;omega
  have hjreal : (2 : ℝ)*((n+1-2^m : ℕ) : ℝ)+1≤(2 : ℝ)^(m+1) := by
    exact_mod_cast le_of_lt hj
  have hden : 0<(2 : ℝ)^(m+1) := by positivity
  change 0≤(2*((n+1-2^m : ℕ) : ℝ)+1)/(2 : ℝ)^(m+1) ∧ _
  constructor
  · positivity
  · exact (div_le_one hden).mpr hjreal

private theorem q_zero : qSeq 0=1/2 := by norm_num [qSeq]

private theorem q_subsequence (m : ℕ) :
    qSeq (3*2^m-1)=1/2+(1/4)*(1/2 : ℝ)^m := by
  have hp : 0<(2 : ℕ)^m := pow_pos (by decide) m
  have hlog : Nat.log 2 (3*2^m)=m+1 := by
    apply (Nat.log_eq_iff (Or.inr ⟨by decide,by positivity⟩)).mpr
    constructor <;> simp only [pow_succ] <;> omega
  have hidx : 3*2^m-1+1=3*2^m := by omega
  have hsub : 3*2^m-2^(m+1)=2^m := by rw [pow_succ];omega
  simp only [qSeq,hidx,hlog,hsub,Nat.cast_pow,Nat.cast_ofNat]
  rw [pow_succ,pow_succ,one_div_pow]
  field_simp
  <;> ring

private theorem not_discrete_scaled_resonances (c : ℝ) (hc : c≠0) :
    ¬ IsDiscrete (Set.range fun n => c*qSeq n) := by
  intro hD
  have hbase : c*qSeq 0∈Set.range (fun n => c*qSeq n) := ⟨0,rfl⟩
  obtain ⟨U,hU,hUsingle⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hD _ hbase
  have hbaseU : c*qSeq 0∈U :=
    (show c*qSeq 0∈U ∩ Set.range (fun n => c*qSeq n) by rw [hUsingle];simp).1
  have ht : Tendsto (fun m : ℕ => c*qSeq (3*2^m-1)) atTop (𝓝 (c*qSeq 0)) := by
    simp only [q_subsequence,q_zero]
    convert tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num)))) using 1 <;> norm_num
  have hevent : ∀ᶠ m in atTop,c*qSeq (3*2^m-1)∈U := ht.eventually (hU.mem_nhds hbaseU)
  obtain ⟨m,hm⟩ := hevent.exists
  have heq : c*qSeq (3*2^m-1)=c*qSeq 0 := by
    apply Set.mem_singleton_iff.mp
    rw [← hUsingle]
    exact ⟨hm,⟨3*2^m-1,rfl⟩⟩
  apply (mul_left_cancel₀ hc) at heq
  rw [q_subsequence,q_zero] at heq
  have hp : 0<(1/2 : ℝ)^m := pow_pos (by norm_num) m
  nlinarith

private theorem isolate_component (n m : ℕ) (t s : ℝ)
    (ht : t∈Set.Icc (lo n) (hi n)) (hs : s∈Set.Icc (lo m) (hi m))
    (hd : |t-s|<rSeq n/4) : m=n := by
  have hr := radius_positive n
  have hds := abs_lt.mp hd
  rcases lt_trichotomy m n with h | h | h
  · have hh := radius_separation h
    dsimp [lo,hi] at ht hs
    linarith [ht.2,hs.1,hds.1]
  · exact h
  · have hh := radius_separation h
    dsimp [lo,hi] at ht hs
    linarith [ht.1,hs.2,hds.2]

private theorem isolate_sum_components (n m k : ℕ) (s t : ℝ)
    (hs : s∈Set.Icc (lo m) (hi m)) (ht : t∈Set.Icc (lo k) (hi k))
    (hd : |(s+t)-2*mid n|<rSeq n/4) : m=n ∧ k=n := by
  have hr := radius_positive n
  have hm := radius_positive m
  have hk := radius_positive k
  have hh := abs_lt.mp hd
  dsimp [lo,hi,mid] at hs ht hh
  have hmn : n≤m := by
    by_contra h
    have hc := radius_separation (show m<n by omega)
    linarith [hs.1,ht.1,hh.2]
  have hkn : n≤k := by
    by_contra h
    have hc := radius_separation (show k<n by omega)
    linarith [hs.1,ht.1,hh.2]
  have hrm : rSeq m≤rSeq n := by
    rcases hmn.eq_or_lt with h | h
    · simpa [h]
    · have hc := radius_separation h;linarith
  have hrk : rSeq k≤rSeq n := by
    rcases hkn.eq_or_lt with h | h
    · simpa [h]
    · have hc := radius_separation h;linarith
  constructor
  · by_contra h
    have hc := radius_separation (show n<m by omega)
    linarith [hs.2,ht.2,hh.1]
  · by_contra h
    have hc := radius_separation (show n<k by omega)
    linarith [hs.2,ht.2,hh.1]

open scoped Pointwise
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
private def singleWord {Y : Type} (z : Y) : Word Y := ⟨1,fun _ => z⟩
private def pairWord {Y : Type} (u v : Y) : Word Y := ⟨2,![u,v]⟩
private def orderedPair {k ℓ : ℕ} (x : (EuclideanSpace ℝ (Fin k))) (y : (EuclideanSpace ℝ (Fin ℓ))) : (EuclideanSpace ℝ (Fin (k+ℓ))) :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

private theorem block_transfer_append {k ℓ : ℕ} (x : (EuclideanSpace ℝ (Fin k))) (y : (EuclideanSpace ℝ (Fin ℓ))) (E : ℝ) :
    blockTransfer (orderedPair x y) E=blockTransfer y E*blockTransfer x E := by
  change (List.ofFn (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))).foldl _ 1 = _
  rw [List.ofFn_fin_append,List.foldl_append]
  exact foldLeftStart _ _ _

private theorem neg_identity_trace_bound (n : ℕ) :
    |Matrix.trace ((-1 : (Matrix (Fin 2) (Fin 2) ℝ))^n)|≤2 := by
  have heq : (-1 : (Matrix (Fin 2) (Fin 2) ℝ))^n=((-1 : ℝ)^n) • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
    simpa using (smul_pow (-1 : ℝ) (1 : (Matrix (Fin 2) (Fin 2) ℝ)) n)
  rw [heq,Matrix.trace_smul,smul_eq_mul,abs_mul]
  norm_num [Matrix.trace_fin_two,abs_pow]

private theorem neg_j_trace_bound (n : ℕ) :
    |Matrix.trace ((-(transfer 0 0))^n)|≤2 := by
  have hsq : (-(transfer 0 0))^2=-(1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
    simpa [pow_two] using j_square
  have hfour : (-(transfer 0 0))^4=(1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [show (4 : ℕ)=2*2 from rfl,pow_mul,hsq]
    simp
  rw [← Nat.mod_add_div n 4,pow_add,pow_mul,hfour,one_pow,mul_one]
  have hmod : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases hmod with h | h | h | h <;> rw [h]
  · norm_num [Matrix.trace_fin_two]
  · norm_num [transfer,Matrix.trace_fin_two]
  · rw [hsq];norm_num [Matrix.trace_fin_two]
  · rw [show (3 : ℕ)=2+1 from rfl,pow_add,hsq]
    norm_num [transfer,Matrix.trace_fin_two]

private theorem single_word_close {k : ℕ} (z : (EuclideanSpace ℝ (Fin k))) (y : Word ((EuclideanSpace ℝ (Fin k)))) (ε : ℝ)
    (hy : wordDistance (singleWord z) y<ε) (i : Fin (y.length : ℕ)) :
    dist z (y.letter i)<ε := by
  have hh := (wordDistanceLtIff (singleWord z) y ε).mp hy i.val
  simpa [singleWord,periodicLetter,Nat.mod_eq_of_lt i.isLt] using hh

private theorem pair_word_periodic {Y : Type} (u v : Y) (j : ℕ) :
    periodicLetter (pairWord u v) j=if j%2=0 then u else v := by
  have hmod : j%2=0 ∨ j%2=1 := by exact Nat.mod_two_eq_zero_or_one j
  rcases hmod with h | h <;> simp [periodicLetter,pairWord,h]

private theorem not_gap_rich_of_obstructions {k : ℕ} (X : Set ((EuclideanSpace ℝ (Fin k)))) (Q : Set ℝ)
    (hQ : ¬ IsDiscrete Q)
    (hobs : ∀ E∈Q,∃ x : Word ((EuclideanSpace ℝ (Fin k))),WordOver X x ∧
      ∃ ε : ℝ,0<ε ∧ ∀ y : Word ((EuclideanSpace ℝ (Fin k))),WordOver X y → wordDistance x y<ε →
        |Matrix.trace (extend blockTransfer y E)|≤2) : ¬ GapRich X := by
  rintro ⟨S,hS,hGR⟩
  apply hQ (hS.mono ?_)
  intro E hE
  by_contra hES
  obtain ⟨x,hx,ε,hε,hbound⟩ := hobs E hE
  obtain ⟨y,hy,hclose,hhyp⟩ := hGR E hES x hx ε hε
  exact (not_lt_of_ge (hbound y hy hclose)) hhyp

private def sumCenter (h : ℝ) (n : ℕ) : (EuclideanSpace ℝ (Fin 3)) :=
  lBlock h (qSeq n) (mid n)+lBlock (-h) (qSeq n) (mid n)
private def productCenter (h : ℝ) (n : ℕ) : (EuclideanSpace ℝ (Fin 10)) :=
  orderedPair (uBlock h (qSeq n) (mid n)) (vBlock h (qSeq n) (mid n))

private theorem sum_center_member (h : ℝ) (n : ℕ) : sumCenter h n ∈ (componentAlphabet (lBlock h) qSeq lo hi)+(componentAlphabet (lBlock (-h)) qSeq lo hi) := by
  exact Set.mem_add.mpr ⟨lBlock h (qSeq n) (mid n),⟨n,mid n,midpoint_member n,rfl⟩,
    lBlock (-h) (qSeq n) (mid n),⟨n,mid n,midpoint_member n,rfl⟩,rfl⟩

private theorem sum_near_resonance (h : ℝ) (n : ℕ) (z : (EuclideanSpace ℝ (Fin 3)))
    (hz : z∈(componentAlphabet (lBlock h) qSeq lo hi)+(componentAlphabet (lBlock (-h)) qSeq lo hi)) (hd : dist (sumCenter h n) z<rSeq n/4) :
    blockTransfer z (2*qSeq n)=-(transfer 0 0) := by
  obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_add.mp hz
  obtain ⟨m,s,hs,rfl⟩ := hx
  obtain ⟨k,t,ht,rfl⟩ := hy
  have hc := lt_of_le_of_lt (PiLp.dist_apply_le
    (sumCenter h n) (lBlock h (qSeq m) s+lBlock (-h) (qSeq k) t) (0 : Fin 3)) hd
  have hsum : |(s+t)-2*mid n|<rSeq n/4 := by
    simpa [sumCenter,lBlock,PiLp.add_apply,Real.dist_eq,abs_sub_comm,two_mul] using hc
  obtain ⟨hm,hk⟩ := isolate_sum_components n m k s t hs ht hsum
  subst m k
  exact sum_transfer_resonance h (qSeq n) s t

private theorem sum_not_gap_rich (h : ℝ) : ¬ GapRich ((componentAlphabet (lBlock h) qSeq lo hi)+(componentAlphabet (lBlock (-h)) qSeq lo hi)) := by
  apply not_gap_rich_of_obstructions _ (Set.range fun n => 2*qSeq n)
    (not_discrete_scaled_resonances 2 (by norm_num))
  rintro E ⟨n,rfl⟩
  refine ⟨singleWord (sumCenter h n),(fun i => sum_center_member h n),rSeq n/4,
    div_pos (radius_positive n) (by norm_num),?_⟩
  intro y hy hclose
  have hletters : ∀ z∈List.ofFn y.letter,blockTransfer z (2*qSeq n)=-(transfer 0 0) := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact sum_near_resonance h n _ (hy i) (single_word_close _ y _ hclose i)
  unfold extend
  rw [fold_constant _ _ _ hletters,List.length_ofFn]
  exact neg_j_trace_bound _

private theorem product_center_member (h : ℝ) (n : ℕ) :
    productCenter h n ∈ cartesianProduct ((componentAlphabet (uBlock h) qSeq lo hi)) ((componentAlphabet (vBlock h) qSeq lo hi)) := by
  exact ⟨uBlock h (qSeq n) (mid n),⟨n,mid n,midpoint_member n,rfl⟩,
    vBlock h (qSeq n) (mid n),⟨n,mid n,midpoint_member n,rfl⟩,rfl⟩

private theorem product_near_resonance (h : ℝ) (n : ℕ) (z : (EuclideanSpace ℝ (Fin 10)))
    (hz : z∈cartesianProduct ((componentAlphabet (uBlock h) qSeq lo hi)) ((componentAlphabet (vBlock h) qSeq lo hi))) (hd : dist (productCenter h n) z<rSeq n/4) :
    blockTransfer z (qSeq n)=-(1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
  obtain ⟨x,hx,y,hy,rfl⟩ := hz
  obtain ⟨m,s,hs,rfl⟩ := hx
  obtain ⟨k,t,ht,rfl⟩ := hy
  have hc₁ := lt_of_le_of_lt (PiLp.dist_apply_le (productCenter h n)
    (orderedPair (uBlock h (qSeq m) s) (vBlock h (qSeq k) t)) (0 : Fin 10)) hd
  have hc₂ := lt_of_le_of_lt (PiLp.dist_apply_le (productCenter h n)
    (orderedPair (uBlock h (qSeq m) s) (vBlock h (qSeq k) t)) (6 : Fin 10)) hd
  have hsclose : |mid n-s|<rSeq n/4 := by
    exact RCLike.ofReal_lt_ofReal.mp hc₁
  have htclose : |mid n-t|<rSeq n/4 := by
    exact RCLike.ofReal_lt_ofReal.mp hc₂
  have hm := isolate_component n m (mid n) s (midpoint_member n) hs hsclose
  have hk := isolate_component n k (mid n) t (midpoint_member n) ht htclose
  subst m k
  rw [show WithLp.toLp 2 (Fin.append (WithLp.ofLp (uBlock h (qSeq n) s))
    (WithLp.ofLp (vBlock h (qSeq n) t)))=orderedPair (uBlock h (qSeq n) s) (vBlock h (qSeq n) t) from rfl,
    block_transfer_append]
  exact cancellation_resonance h (qSeq n) s t

private theorem product_not_gap_rich (h : ℝ) : ¬ GapRich (cartesianProduct ((componentAlphabet (uBlock h) qSeq lo hi)) ((componentAlphabet (vBlock h) qSeq lo hi))) := by
  apply not_gap_rich_of_obstructions _ (Set.range qSeq)
    (by simpa using not_discrete_scaled_resonances 1 (by norm_num))
  rintro E ⟨n,rfl⟩
  refine ⟨singleWord (productCenter h n),(fun i => product_center_member h n),rSeq n/4,
    div_pos (radius_positive n) (by norm_num),?_⟩
  intro y hy hclose
  have hletters : ∀ z∈List.ofFn y.letter,blockTransfer z (qSeq n)=-(1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact product_near_resonance h n _ (hy i) (single_word_close _ y _ hclose i)
  unfold extend
  rw [fold_constant _ _ _ hletters,List.length_ofFn]
  exact neg_identity_trace_bound _

open scoped Pointwise
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem union_near_u_resonance (h : ℝ) (n : ℕ) (z : (EuclideanSpace ℝ (Fin 5)))
    (hz : z∈(componentAlphabet (uBlock h) qSeq lo hi) ∪ (componentAlphabet (vBlock h) qSeq lo hi)) (hd : dist (uBlock h (qSeq n) (mid n)) z<rSeq n/4) :
    blockTransfer z (qSeq n)=transfer 0 h := by
  rcases hz with hz | hz
  · obtain ⟨m,t,ht,rfl⟩ := hz
    have hc := lt_of_le_of_lt (PiLp.dist_apply_le
      (uBlock h (qSeq n) (mid n)) (uBlock h (qSeq m) t) (0 : Fin 5)) hd
    have hd' : |mid n-t|<rSeq n/4 := by exact RCLike.ofReal_lt_ofReal.mp hc
    have hm := isolate_component n m (mid n) t (midpoint_member n) ht hd'
    subst m
    exact u_transfer_resonance h (qSeq n) t
  · obtain ⟨m,t,ht,rfl⟩ := hz
    have hc := lt_of_le_of_lt (PiLp.dist_apply_le
      (uBlock h (qSeq n) (mid n)) (vBlock h (qSeq m) t) (0 : Fin 5)) hd
    have hd' : |mid n-qSeq m|<rSeq n/4 := by exact RCLike.ofReal_lt_ofReal.mp hc
    have hr := radius_positive n
    have hr1 := radius_le_one n
    have hq := (q_bounds m).2
    have hupper := (abs_lt.mp hd').2
    dsimp [mid] at hupper
    linarith

private theorem union_near_v_resonance (h : ℝ) (n : ℕ) (z : (EuclideanSpace ℝ (Fin 5)))
    (hz : z∈(componentAlphabet (uBlock h) qSeq lo hi) ∪ (componentAlphabet (vBlock h) qSeq lo hi)) (hd : dist (vBlock h (qSeq n) (mid n)) z<rSeq n/4) :
    blockTransfer z (qSeq n)=-(Matrix.adjugate (transfer 0 h)) := by
  rcases hz with hz | hz
  · obtain ⟨m,t,ht,rfl⟩ := hz
    have hc := lt_of_le_of_lt (PiLp.dist_apply_le
      (vBlock h (qSeq n) (mid n)) (uBlock h (qSeq m) t) (0 : Fin 5)) hd
    have hd' : |qSeq n-t|<rSeq n/4 := by exact RCLike.ofReal_lt_ofReal.mp hc
    have hr := radius_positive m
    have hr1 := radius_le_one n
    have hq := (q_bounds n).2
    have hlower := (abs_lt.mp hd').1
    dsimp [lo] at ht
    linarith [ht.1]
  · obtain ⟨m,t,ht,rfl⟩ := hz
    have hc := lt_of_le_of_lt (PiLp.dist_apply_le
      (vBlock h (qSeq n) (mid n)) (vBlock h (qSeq m) t) (1 : Fin 5)) hd
    have hd' : |mid n-t|<rSeq n/4 := by exact RCLike.ofReal_lt_ofReal.mp hc
    have hm := isolate_component n m (mid n) t (midpoint_member n) ht hd'
    subst m
    exact v_transfer_resonance h (qSeq n) t

private theorem alternating_list (n : ℕ) (A B : (Matrix (Fin 2) (Fin 2) ℝ)) :
    List.ofFn (fun i : Fin (n*2) => if i.val%2=0 then A else B)=
      (List.replicate n [A,B]).flatten := by
  rw [List.ofFn_mul]
  have heq : (fun i : Fin n => List.ofFn (fun j : Fin 2 =>
      if (i.val*2+j.val)%2=0 then A else B))=(fun _ : Fin n => [A,B]) := by
    funext i
    simp [List.ofFn_succ,Nat.add_mod,Nat.mul_mod]
  rw [heq,List.ofFn_const]

private theorem pairs_fold (n : ℕ) (A B : (Matrix (Fin 2) (Fin 2) ℝ)) :
    ((List.replicate n [A,B]).flatten).foldl (fun M C => C*M) 1=(B*A)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.flatten_cons,List.foldl_append,List.foldl_cons,
      List.foldl_nil,mul_one]
    rw [foldLeftStart,ih,pow_succ]

private theorem alternating_even_fold (m : ℕ) (hm : m%2=0) (A B : (Matrix (Fin 2) (Fin 2) ℝ)) :
    (List.ofFn (fun i : Fin m => if i.val%2=0 then A else B)).foldl
      (fun M C => C*M) 1=(B*A)^(m/2) := by
  have hlen : m=(m/2)*2 := by omega
  conv_lhs => rw [hlen]
  rw [alternating_list,pairs_fold]

private theorem union_word_bound (h : ℝ) (hh : 2<h) (n : ℕ) (y : Word ((EuclideanSpace ℝ (Fin 5))))
    (hy : WordOver ((componentAlphabet (uBlock h) qSeq lo hi) ∪ (componentAlphabet (vBlock h) qSeq lo hi)) y)
    (hd : wordDistance (pairWord (uBlock h (qSeq n) (mid n))
      (vBlock h (qSeq n) (mid n))) y<rSeq n/4) :
    |Matrix.trace (extend blockTransfer y (qSeq n))|≤2 := by
  let u := uBlock h (qSeq n) (mid n)
  let v := vBlock h (qSeq n) (mid n)
  have hall := (wordDistanceLtIff (pairWord u v) y (rSeq n/4)).mp hd
  have heven : (y.length : ℕ)%2=0 := by
    by_contra hmod
    have hodd : (y.length : ℕ)%2=1 := by exact Nat.mod_two_ne_zero.mp hmod
    let i : Fin (y.length : ℕ) := ⟨0,y.length.pos⟩
    have hc₀ : dist u (y.letter i)<rSeq n/4 := by
      have hc := hall 0
      rw [pair_word_periodic] at hc
      simpa [periodicLetter,i] using hc
    have hc₁ : dist v (y.letter i)<rSeq n/4 := by
      have hc := hall (y.length : ℕ)
      rw [pair_word_periodic] at hc
      simpa [hodd,periodicLetter,i] using hc
    have hu := union_near_u_resonance h n _ (hy i) hc₀
    have hv := union_near_v_resonance h n _ (hy i) hc₁
    have heq := congrArg Matrix.trace (hu.symm.trans hv)
    simp [transfer,Matrix.adjugate_fin_two,Matrix.trace_fin_two] at heq
    linarith
  have hletter : ∀ i : Fin (y.length : ℕ),blockTransfer (y.letter i) (qSeq n)=
      if i.val%2=0 then transfer 0 h else -(Matrix.adjugate (transfer 0 h)) := by
    intro i
    have hc := hall i.val
    have hpy : periodicLetter y i.val=y.letter i := by
      simp [periodicLetter,Nat.mod_eq_of_lt i.isLt]
    rw [pair_word_periodic,hpy] at hc
    by_cases hi : i.val%2=0
    · simp only [hi,ite_true] at hc ⊢
      exact union_near_u_resonance h n _ (hy i) hc
    · simp only [hi,ite_false] at hc ⊢
      exact union_near_v_resonance h n _ (hy i) hc
  have hmatrix : extend blockTransfer y (qSeq n)=(-1 : (Matrix (Fin 2) (Fin 2) ℝ))^((y.length : ℕ)/2) := by
    calc
      _ = (List.map (fun z => blockTransfer z (qSeq n)) (List.ofFn y.letter)).foldl
          (fun M C => C*M) 1 := by simp only [List.foldl_map];rfl
      _ = (List.ofFn (fun i : Fin (y.length : ℕ) => if i.val%2=0 then transfer 0 h
          else -(Matrix.adjugate (transfer 0 h)))).foldl (fun M C => C*M) 1 := by
            rw [List.map_ofFn]
            congr 2
            funext i
            exact hletter i
      _ = _ := by
        rw [alternating_even_fold _ heven,neg_mul,Matrix.adjugate_mul,transfer_det,one_smul]
  rw [hmatrix]
  exact neg_identity_trace_bound _

private theorem union_not_gap_rich (h : ℝ) (hh : 2<h) : ¬ GapRich ((componentAlphabet (uBlock h) qSeq lo hi) ∪ (componentAlphabet (vBlock h) qSeq lo hi)) := by
  apply not_gap_rich_of_obstructions _ (Set.range qSeq)
    (by simpa using not_discrete_scaled_resonances 1 (by norm_num))
  rintro E ⟨n,rfl⟩
  refine ⟨pairWord (uBlock h (qSeq n) (mid n)) (vBlock h (qSeq n) (mid n)),?_,
    rSeq n/4,div_pos (radius_positive n) (by norm_num),?_⟩
  · intro i
    fin_cases i
    · exact Or.inl ⟨n,mid n,midpoint_member n,rfl⟩
    · exact Or.inr ⟨n,mid n,midpoint_member n,rfl⟩
  · exact union_word_bound h hh n

theorem result : ¬ claim := by
  intro h
  rcases h with h | h | h
  · exact union_not_gap_rich 3 (by norm_num)
      (h 5 (by norm_num) ((componentAlphabet (uBlock 3) qSeq lo hi)) ((componentAlphabet (vBlock 3) qSeq lo hi))
        (u_gap_rich 3 (by norm_num) qSeq lo hi interval_nonempty)
        (v_gap_rich 3 (by norm_num) qSeq lo hi interval_nonempty))
  · exact sum_not_gap_rich 3
      (h 3 (by norm_num) ((componentAlphabet (lBlock 3) qSeq lo hi)) ((componentAlphabet (lBlock (-3)) qSeq lo hi))
        (l_gap_rich 3 (by norm_num) qSeq lo hi interval_nonempty)
        (l_gap_rich (-3) (by norm_num) qSeq lo hi interval_nonempty))
  · exact product_not_gap_rich 3
      (h 5 5 (by norm_num) (by norm_num) ((componentAlphabet (uBlock 3) qSeq lo hi)) ((componentAlphabet (vBlock 3) qSeq lo hi))
        (u_gap_rich 3 (by norm_num) qSeq lo hi interval_nonempty)
        (v_gap_rich 3 (by norm_num) qSeq lo hi interval_nonempty))


end
end D5.S3.Analytic.Spectral.FillmanLimGapRichClosures
