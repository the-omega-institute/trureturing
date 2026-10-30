/- GID: D5/S3/Observer/CubicGain/FixedDriftQuartic
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/FixedDriftQuartic
   mirror-E: none(waiver:universal-original-world-classification)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: Guarded roots reconstruct all fixed-drift zero-terminal-gain worlds. -/

import D5.S3.Observer.CubicGain.OriginalWorld

/-! Fixed drift and a zero gain at literal clock seven, on the full original carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain.FixedDriftQuartic
open Polynomial

def aPoly (d : ℝ) : ℝ[X] :=
  C (-225*d)*X^2 + C (33894-1310*d)*X + C (175*d-3150)
def bPoly (d : ℝ) : ℝ[X] :=
  C (75*d)*X^2 + C (46494-1710*d)*X + C (9450-525*d)
def zPoly (d : ℝ) : ℝ[X] :=
  C (-225*d)*X^2 - C (14490+750*d)*X + C (47250-2625*d)
def yPoly (d : ℝ) : ℝ[X] :=
  C (-600*d)*X^2 + C (240*d-72576)*X + C (75600-4200*d)
def kPoly : ℝ[X] := 4200*X*(X+1)
def lPoly (d : ℝ) : ℝ[X] := 12*aPoly d*bPoly d
def nPoly (d : ℝ) : ℝ[X] := C (24-d)*kPoly*(3*aPoly d-2*bPoly d)
def rPoly (d : ℝ) : ℝ[X] :=
  4*nPoly d^2 - 4*nPoly d*lPoly d +
    4*(X-1)*C (24-d)*kPoly*bPoly d*lPoly d - (X-1)^2*lPoly d^2
def ePoly (d p : ℝ) : ℝ[X] :=
  C (2100*(p-d))*(X+1)*bPoly d -
    zPoly d*(bPoly d+C (1050*(24-d))*(X+1))
def fPoly (d v : ℝ) : ℝ[X] :=
  C (4200*(v-d))*(X+1)*bPoly d -
    yPoly d*(2*bPoly d+C (1050*(24-d))*(X+1))

def A (d u : ℝ) : ℝ := (aPoly d).eval u
def B (d u : ℝ) : ℝ := (bPoly d).eval u
def Z (d u : ℝ) : ℝ := (zPoly d).eval u
def Y (d u : ℝ) : ℝ := (yPoly d).eval u
def K (u : ℝ) : ℝ := kPoly.eval u
def L (d u : ℝ) : ℝ := (lPoly d).eval u
def N (d u : ℝ) : ℝ := (nPoly d).eval u

def Guard (d u : ℝ) : Prop :=
  1 < u ∧ A d u * B d u ≠ 0 ∧ 0 < N d u/L d u ∧ N d u/L d u < 1

def S (d p v : ℝ) : Set ℝ :=
  {u | Guard d u ∧ (rPoly d).eval u = 0 ∧
    (ePoly d p).eval u = 0 ∧ (fPoly d v).eval u = 0}

/-- Only the first five readings are fixed in this set. -/
def PrefixWorlds (d : ℝ) : Set OriginalWorld :=
  {W | OriginalParent W ∧ W.2.2.1 = d ∧ (originalPolynomial W).eval 7 = 0}

/-- The entire seven-reading child, with its actual drift and terminal gain. -/
def ChildWorlds (d p v : ℝ) : Set OriginalWorld :=
  {W | W ∈ PrefixWorlds d ∧ originalRead W 5 = p ∧ originalRead W 6 = v}

def width (u : ℝ) : ℝ := (u-1)/2
def j (d u : ℝ) : ℝ := (24-d)*K u/(6*A d u)
def n (d u : ℝ) : ℝ := (24-d)*K u/(4*B d u)
def r (d u : ℝ) : ℝ := N d u/L d u
def e0 (d : ℝ) : ℝ := -d/7
def e2 (d u : ℝ) : ℝ := (294-10*d)/(25*(u+1))
def e4 (d u : ℝ) : ℝ := (18-d)/(3*u)

def hPoly (d u : ℝ) : ℝ[X] :=
  C (e0 d/8)*(X-2)*(X-4) - C (e2 d u/4)*X*(X-4) +
    C (e4 d u/8)*X*(X-2)
def gPoly (d u : ℝ) : ℝ[X] := (7-X)*hPoly d u

/-- Equation (3.2), using the existing ordinary-coefficient world carrier. -/
def reconstruct (d u : ℝ) : OriginalWorld :=
  (r d u,width u,d,Polynomial.toFn 4 (gPoly d u))

def coordinate (W : OriginalWorld) : ℝ := 1+2*W.2.1

private theorem read_trace (W : OriginalWorld) (i : ℕ) :
    originalRead W i = W.2.2.1+(originalPolynomial W).eval (i:ℝ)*
      traceAt W.1 W.2.1 i := rfl

private theorem g_degree (d u : ℝ) : (gPoly d u).natDegree ≤ 3 := by
  unfold gPoly hPoly
  compute_degree

private theorem reconstruct_polynomial (d u : ℝ) :
    originalPolynomial (reconstruct d u) = gPoly d u :=
  Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := g_degree d u; omega)

private theorem basic_samples (d u : ℝ) :
    (gPoly d u).eval 0 = -d ∧
    (gPoly d u).eval 2 = 5*e2 d u ∧
    (gPoly d u).eval 4 = 3*e4 d u ∧
    (gPoly d u).eval 7 = 0 := by
  refine ⟨?_,?_,?_,?_⟩ <;> simp [gPoly,hPoly,e0] <;> ring

private theorem odd_samples (d u : ℝ) (hu : 1 < u) :
    (gPoly d u).eval 1 = 6*A d u/K u ∧
    (gPoly d u).eval 3 = 4*B d u/K u ∧
    (gPoly d u).eval 5 = 2*Z d u/K u ∧
    (gPoly d u).eval 6 = Y d u/K u := by
  have h0 : u ≠ 0 := by linarith
  have h1 : u+1 ≠ 0 := by linarith
  simp [gPoly,hPoly,e0,e2,e4,A,B,Z,Y,K,aPoly,bPoly,zPoly,yPoly,kPoly]
  constructor
  · field_simp [h0,h1]; ring
  constructor
  · field_simp [h0,h1]; ring
  constructor
  · field_simp [h0,h1]; ring
  · field_simp [h0,h1]; ring

private theorem denominators (d u : ℝ) (h : Guard d u) :
    A d u ≠ 0 ∧ B d u ≠ 0 ∧ L d u ≠ 0 ∧ K u ≠ 0 ∧ width u ≠ 0 := by
  obtain ⟨hu,hab,_,_⟩ := h
  have ha := (mul_ne_zero_iff.mp hab).1
  have hb := (mul_ne_zero_iff.mp hab).2
  refine ⟨ha,hb,?_,?_,?_⟩
  · simpa [L,lPoly,A,B] using mul_ne_zero (mul_ne_zero (by norm_num : (12:ℝ) ≠ 0) ha) hb
  · dsimp [K,kPoly]
    simp only [eval_mul,eval_ofNat,eval_X,eval_add,eval_one]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by linarith)) (by linarith)
  · dsimp [width]; exact div_ne_zero (by linarith) (by norm_num)

private theorem n_sub_j (d u : ℝ) (ha : A d u ≠ 0) (hb : B d u ≠ 0) :
    n d u-j d u = r d u := by
  have hN : N d u = (24-d)*K u*(3*A d u-2*B d u) := by
    simp [N,nPoly,A,B,K]
  have hL : L d u = 12*A d u*B d u := by simp [L,lPoly,A,B]
  dsimp [n,j,r]
  rw [hN,hL]
  field_simp [ha,hb]
  <;> ring

private theorem rank_equivalence (d u : ℝ) (ha : A d u ≠ 0) (hb : B d u ≠ 0) :
    (rPoly d).eval u = 0 ↔ r d u*(1-r d u) = width u*(j d u-width u) := by
  have hL : L d u = 12*A d u*B d u := by simp [L,lPoly,A,B]
  have hl : L d u ≠ 0 := by
    rw [hL]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  have identity : (rPoly d).eval u =
      -4*(L d u)^2*(r d u*(1-r d u)-width u*(j d u-width u)) := by
    simp only [rPoly,eval_sub,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one,eval_C]
    change 4*N d u^2-4*N d u*L d u+
      4*(u-1)*(24-d)*K u*B d u*L d u-(u-1)^2*L d u^2 = _
    dsimp [r,width,j]
    rw [hL]
    field_simp [ha,hb]
    <;> ring
  rw [identity]
  have hn : -4*(L d u)^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hl)
  simp only [mul_eq_zero,hn,false_or,sub_eq_zero]

private theorem prefix_gain (d : ℝ) (W : OriginalWorld)
    (hW : W ∈ PrefixWorlds d) :
    originalPolynomial W = gPoly d (coordinate W) := by
  obtain ⟨hp,hd,h7⟩ := hW
  let u := coordinate W
  have hu : 1 < u := by dsimp [u,coordinate]; linarith [hp.2.2.1]
  have hu0 : u ≠ 0 := by linarith
  have hu1 : u+1 ≠ 0 := by linarith
  have ht0 := congrFun (literal_traces W.1 W.2.1) (0 : Fin 7)
  have ht2 := congrFun (literal_traces W.1 W.2.1) (2 : Fin 7)
  have ht4 := congrFun (literal_traces W.1 W.2.1) (4 : Fin 7)
  norm_num at ht0 ht2 ht4
  have row0 := hp.2.2.2.2 (0 : Fin 5)
  have row2 := hp.2.2.2.2 (2 : Fin 5)
  have row4 := hp.2.2.2.2 (4 : Fin 5)
  rw [read_trace] at row0 row2 row4
  norm_num [ht0,ht2,ht4,history,hd] at row0 row2 row4
  have h0 : (originalPolynomial W).eval 0 = -d := by linarith
  have h2 : (originalPolynomial W).eval 2 = 5*e2 d u := by
    apply (mul_right_cancel₀ (by linarith [hp.2.2.1] : (1+W.2.1) ≠ 0))
    have he : 5*e2 d u*(1+W.2.1) = 147/5-d := by
      have heU : u+1 = 2*(1+W.2.1) := by dsimp [u,coordinate]; ring
      dsimp [e2]
      rw [heU]
      field_simp [show 1+W.2.1 ≠ 0 by linarith [hp.2.2.1]]
      <;> ring
    rw [he]
    linarith
  have h4 : (originalPolynomial W).eval 4 = 3*e4 d u := by
    apply (mul_right_cancel₀ hu0)
    have he : 3*e4 d u*u = 18-d := by
      dsimp [e4]; field_simp [hu0]
    rw [he]
    change d+(originalPolynomial W).eval 4*u=18 at row4
    linarith
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s := {0,2,4,7})
  · simpa [originalPolynomial] using (Polynomial.ofFn_degree_lt W.2.2.2)
  · have hh := degree_le_of_natDegree_le (g_degree d u)
    simpa using lt_of_le_of_lt hh (show (3 : WithBot ℕ) < 4 by norm_num)
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    obtain rfl | rfl | rfl | rfl := hx
    · exact h0.trans (basic_samples d u).1.symm
    · exact h2.trans (basic_samples d u).2.1.symm
    · exact h4.trans (basic_samples d u).2.2.1.symm
    · exact h7.trans (basic_samples d u).2.2.2.symm

private theorem prefix_coordinates (d : ℝ) (hd24 : d ≠ 24)
    (W : OriginalWorld) (hW : W ∈ PrefixWorlds d) :
    Guard d (coordinate W) ∧ (rPoly d).eval (coordinate W) = 0 ∧
      reconstruct d (coordinate W) = W := by
  let u := coordinate W
  obtain ⟨hp,hd,h7⟩ := hW
  have hu : 1 < u := by dsimp [u,coordinate]; linarith [hp.2.2.1]
  have hu0 : u ≠ 0 := by linarith
  have hu1 : u+1 ≠ 0 := by linarith
  have hk : K u ≠ 0 := by
    simp [K,kPoly,hu0,hu1]
  have hg := prefix_gain d W ⟨hp,hd,h7⟩
  have hs := odd_samples d u hu
  have ht1 := congrFun (literal_traces W.1 W.2.1) (1 : Fin 7)
  have ht3 := congrFun (literal_traces W.1 W.2.1) (3 : Fin 7)
  norm_num at ht1 ht3
  have row1 := hp.2.2.2.2 (1 : Fin 5)
  have row3 := hp.2.2.2.2 (3 : Fin 5)
  rw [read_trace] at row1 row3
  norm_num [history,hd,hg,ht1,ht3,hs.1,hs.2.1] at row1 row3
  change d+(gPoly d u).eval 1*sourceJ W.1 W.2.1=24 at row1
  change d+(gPoly d u).eval 3*sourceN W.1 W.2.1=24 at row3
  rw [hs.1] at row1
  rw [hs.2.1] at row3
  have ha : A d u ≠ 0 := by
    intro hz
    rw [hz] at row1
    simp at row1
    exact hd24 row1
  have hb : B d u ≠ 0 := by
    intro hz
    rw [hz] at row3
    simp at row3
    exact hd24 row3
  have hj : sourceJ W.1 W.2.1 = j d u := by
    dsimp [j]
    apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
    field_simp [hk] at row1
    nlinarith only [row1]
  have hn : sourceN W.1 W.2.1 = n d u := by
    dsimp [n]
    apply (eq_div_iff (mul_ne_zero (by norm_num) hb)).mpr
    field_simp [hk] at row3
    nlinarith only [row3]
  have hr : r d u = W.1 := by
    rw [← n_sub_j d u ha hb,← hn,← hj]
    simp [sourceN]
  have hw : width u = W.2.1 := by dsimp [width,u,coordinate]; ring
  have hgU : Guard d u := ⟨hu,mul_ne_zero ha hb,by change 0 < r d u; rw [hr]; exact hp.1,
    by change r d u < 1; rw [hr]; exact hp.2.1⟩
  have hR : (rPoly d).eval u = 0 := by
    apply (rank_equivalence d u ha hb).mpr
    rw [hr,hw,← hj]
    dsimp [sourceJ]
    field_simp [ne_of_gt hp.2.2.1]
    <;> ring
  refine ⟨hgU,hR,?_⟩
  apply Prod.ext hr
  apply Prod.ext hw
  apply Prod.ext hd.symm
  apply Polynomial.injective_ofFn 4
  change originalPolynomial (reconstruct d u) = originalPolynomial W
  rw [reconstruct_polynomial,hg]

private theorem reconstructed_traces (d u : ℝ) (hg : Guard d u)
    (hR : (rPoly d).eval u = 0) :
    sourceJ (r d u) (width u) = j d u ∧
    sourceN (r d u) (width u) = n d u := by
  obtain ⟨ha,hb,_,_,hw⟩ := denominators d u hg
  have he := (rank_equivalence d u ha hb).mp hR
  have hj : sourceJ (r d u) (width u) = j d u := by
    dsimp [sourceJ]
    have hq : r d u*(1-r d u)/width u = j d u-width u :=
      (div_eq_iff hw).mpr (by nlinarith only [he])
    rw [hq]
    ring
  refine ⟨hj,?_⟩
  dsimp [sourceN]
  rw [hj,← n_sub_j d u ha hb]
  ring

private theorem reconstructed_read (d u : ℝ) (hg : Guard d u)
    (hR : (rPoly d).eval u = 0) :
    (fun i : Fin 7 => originalRead (reconstruct d u) i) =
      ![d+(gPoly d u).eval 0,
        d+(gPoly d u).eval 1*j d u,
        d+(gPoly d u).eval 2*((u+1)/2),
        d+(gPoly d u).eval 3*n d u,
        d+(gPoly d u).eval 4*u,
        d+(gPoly d u).eval 5*(u+n d u),
        d+(gPoly d u).eval 6*(2*u+n d u)] := by
  obtain ⟨hj,hn⟩ := reconstructed_traces d u hg hR
  have hT : 1+width u = (u+1)/2 := by dsimp [width]; ring
  have hU : 1+2*width u = u := by dsimp [width]; ring
  ext i
  change d+(originalPolynomial (reconstruct d u)).eval ((i : ℕ):ℝ)*
    traceAt (r d u) (width u) i = _
  rw [reconstruct_polynomial]
  have ht := congrFun (literal_traces (r d u) (width u)) i
  rw [ht,hj,hn,hT,hU]
  fin_cases i <;> norm_num

private theorem reconstruct_prefix (d u : ℝ) (hd0 : d ≠ 0)
    (hg : Guard d u) (hR : (rPoly d).eval u = 0) :
    reconstruct d u ∈ PrefixWorlds d := by
  obtain ⟨ha,hb,_,hk,_⟩ := denominators d u hg
  have hu0 : u ≠ 0 := by linarith [hg.1]
  have hu1 : u+1 ≠ 0 := by linarith [hg.1]
  have hs := basic_samples d u
  have ho := odd_samples d u hg.1
  have hr := reconstructed_read d u hg hR
  refine ⟨⟨hg.2.2.1,hg.2.2.2,by dsimp [reconstruct,width]; linarith [hg.1],?_,?_⟩,
    rfl,?_⟩
  · rw [reconstruct_polynomial]
    intro hz
    have hh := congrArg (fun q : ℝ[X] => q.eval 0) hz
    rw [hs.1] at hh
    simp at hh
    exact hd0 hh
  · intro i
    have ht := congrFun hr (Fin.castLE (by norm_num : 5 ≤ 7) i)
    fin_cases i <;> norm_num [history] at ht ⊢
    · rw [ht,hs.1]; ring
    · rw [ht,ho.1]
      dsimp [j]
      field_simp [ha,hk]
      <;> ring
    · rw [ht,hs.2.1]
      dsimp [e2]
      field_simp [hu1]
      <;> ring
    · rw [ht,ho.2.1]
      dsimp [n]
      field_simp [hb,hk]
      <;> ring
    · rw [ht,hs.2.2.1]
      dsimp [e4]
      field_simp [hu0]
      <;> ring
  · rw [reconstruct_polynomial]
    exact hs.2.2.2

private theorem late_equivalences (d u p v : ℝ) (hg : Guard d u) :
    (d+(gPoly d u).eval 5*(u+n d u)=p ↔ (ePoly d p).eval u=0) ∧
    (d+(gPoly d u).eval 6*(2*u+n d u)=v ↔ (fPoly d v).eval u=0) := by
  obtain ⟨_,hb,_,_,_⟩ := denominators d u hg
  have hu0 : u ≠ 0 := by linarith [hg.1]
  have hu1 : u+1 ≠ 0 := by linarith [hg.1]
  have hK : K u = 4200*u*(u+1) := by simp [K,kPoly]
  have he : (ePoly d p).eval u = 2100*(u+1)*B d u*
      (p-d-(gPoly d u).eval 5*(u+n d u)) := by
    rw [(odd_samples d u hg.1).2.2.1]
    simp only [ePoly,eval_sub,eval_mul,eval_C,eval_add,eval_X,eval_one]
    change 2100*(p-d)*(u+1)*B d u-
      Z d u*(B d u+1050*(24-d)*(u+1)) = _
    dsimp [n]
    rw [hK]
    field_simp [hu0,hu1,hb]
    <;> ring
  have hf : (fPoly d v).eval u = 4200*(u+1)*B d u*
      (v-d-(gPoly d u).eval 6*(2*u+n d u)) := by
    rw [(odd_samples d u hg.1).2.2.2]
    simp only [fPoly,eval_sub,eval_mul,eval_C,eval_add,eval_X,eval_one,eval_ofNat]
    change 4200*(v-d)*(u+1)*B d u-
      Y d u*(2*B d u+1050*(24-d)*(u+1)) = _
    dsimp [n]
    rw [hK]
    field_simp [hu0,hu1,hb]
    <;> ring
  have hn2 : 2100*(u+1)*B d u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hu1) hb
  have hn4 : 4200*(u+1)*B d u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hu1) hb
  constructor
  · rw [he,mul_eq_zero]
    simp only [hn2,false_or]
    constructor <;> intro h <;> linarith
  · rw [hf,mul_eq_zero]
    simp only [hn4,false_or]
    constructor <;> intro h <;> linarith

private theorem child_coordinates (d p v : ℝ) (hd24 : d ≠ 24)
    (W : OriginalWorld) (hW : W ∈ ChildWorlds d p v) : coordinate W ∈ S d p v := by
  obtain ⟨hg,hR,hw⟩ := prefix_coordinates d hd24 W hW.1
  have hreads := reconstructed_read d (coordinate W) hg hR
  have h5 := congrFun hreads (5 : Fin 7)
  have h6 := congrFun hreads (6 : Fin 7)
  norm_num only [Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk] at h5 h6
  rw [hw] at h5 h6
  exact ⟨hg,hR,(late_equivalences d (coordinate W) p v hg).1.mp
    (h5.symm.trans hW.2.1),(late_equivalences d (coordinate W) p v hg).2.mp
    (h6.symm.trans hW.2.2)⟩

private theorem reconstruct_child (d p v u : ℝ) (hd0 : d ≠ 0)
    (hu : u ∈ S d p v) : reconstruct d u ∈ ChildWorlds d p v := by
  have hp := reconstruct_prefix d u hd0 hu.1 hu.2.1
  have hreads := reconstructed_read d u hu.1 hu.2.1
  have h5 := congrFun hreads (5 : Fin 7)
  have h6 := congrFun hreads (6 : Fin 7)
  norm_num only [Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk] at h5 h6
  exact ⟨hp,h5.trans ((late_equivalences d u p v hu.1).1.mpr hu.2.2.1),
    h6.trans ((late_equivalences d u p v hu.1).2.mpr hu.2.2.2)⟩

private theorem coordinate_injective (d : ℝ) (hd24 : d ≠ 24) :
    Set.InjOn coordinate (PrefixWorlds d) := by
  intro W hW V hV he
  rw [← (prefix_coordinates d hd24 W hW).2.2,
    ← (prefix_coordinates d hd24 V hV).2.2,he]

private theorem r_degree (d : ℝ) : (rPoly d).natDegree ≤ 10 := by
  unfold rPoly nPoly lPoly kPoly aPoly bPoly
  compute_degree

private theorem e_degree (d p : ℝ) : (ePoly d p).natDegree ≤ 4 := by
  unfold ePoly zPoly bPoly
  compute_degree

private theorem r_top (d : ℝ) : (rPoly d).coeff 10 = -41006250000*d^4 := by
  unfold rPoly nPoly lPoly kPoly aPoly bPoly
  compute_degree!
  <;> ring

private theorem e_top (d p : ℝ) : (ePoly d p).coeff 4 = 16875*d^2 := by
  unfold ePoly zPoly bPoly
  compute_degree!
  <;> ring

private theorem prefix_bound (d : ℝ) (hd0 : d ≠ 0) (hd24 : d ≠ 24) :
    (PrefixWorlds d).Finite ∧ (PrefixWorlds d).ncard ≤ 10 := by
  have hP : rPoly d ≠ 0 := by
    intro hz
    have hh := r_top d
    rw [hz] at hh
    simp only [coeff_zero] at hh
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 4 hd0)) hh.symm
  have hmap : Set.MapsTo coordinate (PrefixWorlds d) ((rPoly d).rootSet ℝ) := by
    intro W hW
    rw [mem_rootSet_of_ne hP,aeval_def,Algebra.algebraMap_self,eval₂_id]
    exact (prefix_coordinates d hd24 W hW).2.1
  have hfin := (rPoly d).rootSet_finite ℝ
  exact ⟨hfin.of_injOn hmap (coordinate_injective d hd24),
    (Set.ncard_le_ncard_of_injOn coordinate hmap (coordinate_injective d hd24) hfin).trans
      ((ncard_rootSet_le (rPoly d) ℝ).trans (r_degree d))⟩

private theorem child_bound (d p v : ℝ) (hd0 : d ≠ 0) (hd24 : d ≠ 24) :
    (ChildWorlds d p v).Finite ∧ (ChildWorlds d p v).ncard ≤ 4 := by
  have hP : ePoly d p ≠ 0 := by
    intro hz
    have hh := e_top d p
    rw [hz] at hh
    simp only [coeff_zero] at hh
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)) hh.symm
  have hmap : Set.MapsTo coordinate (ChildWorlds d p v) ((ePoly d p).rootSet ℝ) := by
    intro W hW
    rw [mem_rootSet_of_ne hP,aeval_def,Algebra.algebraMap_self,eval₂_id]
    exact (child_coordinates d p v hd24 W hW).2.2.1
  have hinj : Set.InjOn coordinate (ChildWorlds d p v) :=
    (coordinate_injective d hd24).mono (fun _ h => h.1)
  have hfin := (ePoly d p).rootSet_finite ℝ
  exact ⟨hfin.of_injOn hmap hinj,
    (Set.ncard_le_ncard_of_injOn coordinate hmap hinj hfin).trans
      ((ncard_rootSet_le (ePoly d p) ℝ).trans (e_degree d p))⟩

/-- The exact guarded classification, its prescribed native inverse, and both
cardinality bounds. The parameters p and v are unrestricted real numbers. -/
theorem fixed_drift_classification (d p v : ℝ) (hd0 : d ≠ 0) (hd24 : d ≠ 24) :
    (∃ e : S d p v ≃ ChildWorlds d p v,
      (∀ u, (e u).1 = reconstruct d u.1) ∧
      (∀ W, (e.symm W).1 = coordinate W.1) ∧
      (∀ u : S d p v,
        originalPolynomial (e u).1 = gPoly d u.1 ∧
        sourceJ (e u).1.1 (e u).1.2.1 = j d u.1 ∧
        sourceN (e u).1.1 (e u).1.2.1 = n d u.1)) ∧
    (PrefixWorlds d).Finite ∧ (PrefixWorlds d).ncard ≤ 10 ∧
    (ChildWorlds d p v).Finite ∧ (ChildWorlds d p v).ncard ≤ 4 := by
  let e : S d p v ≃ ChildWorlds d p v := {
    toFun := fun u => ⟨reconstruct d u.1,reconstruct_child d p v u.1 hd0 u.2⟩
    invFun := fun W => ⟨coordinate W.1,child_coordinates d p v hd24 W.1 W.2⟩
    left_inv := by
      intro u
      apply Subtype.ext
      change coordinate (reconstruct d u.1) = u.1
      dsimp [coordinate,reconstruct,width]
      ring
    right_inv := by
      intro W
      apply Subtype.ext
      exact (prefix_coordinates d hd24 W.1 W.2.1).2.2 }
  refine ⟨⟨e,fun _ => rfl,fun _ => rfl,?_⟩,
    (prefix_bound d hd0 hd24).1,(prefix_bound d hd0 hd24).2,
    (child_bound d p v hd0 hd24).1,(child_bound d p v hd0 hd24).2⟩
  intro u
  exact ⟨reconstruct_polynomial d u.1,
    reconstructed_traces d u.1 u.2.1 u.2.2.1⟩

#print axioms fixed_drift_classification

end D5.S3.Observer.CubicGain.FixedDriftQuartic
