/- GID: D5/S3/Observer/CubicGain/PhaseRigidity
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/PhaseRigidity
   mirror-E: none(waiver:actual-chronological-interior-phase-rigidity)
   anchors: []
   utility: none
   digest: Interior signed kernel levels force one strict phase on actual chronological prefixes. -/

import D5.S3.Observer.CubicGain.PrimitiveKernelLattice
import Mathlib.RingTheory.Coprime.Lemmas

/-! Signed auxiliary columns along the original finite native histories. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.PhaseRigidity

open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open D5.S3.Observer.CubicGain.PrefixKernelSigns
open D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open scoped Matrix

private theorem product_append (u v : List Bool) :
    futureProduct (u ++ v) = futureProduct v * futureProduct u := by
  induction u with
  | nil => simp [futureProduct]
  | cons e u ih => simp only [List.cons_append, futureProduct, ih, Matrix.mul_assoc]

private theorem atom_j (v : Fin 2 → ℝ) : actionJ *ᵥ v = ![v 1,v 0] := by
  ext i
  fin_cases i <;> simp [actionJ,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

private theorem atom_m (v : Fin 2 → ℝ) : actionM *ᵥ v = ![v 1,v 0+v 1] := by
  ext i
  fin_cases i <;> simp [actionM,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

private theorem j_square : actionJ * actionJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [actionJ,Matrix.mul_apply,Fin.sum_univ_two]

private def Positive (v : Fin 2 → ℝ) : Prop := 0 < v 0 ∧ 0 < v 1
private def Negative (v : Fin 2 → ℝ) : Prop := v 0 < 0 ∧ v 1 < 0
def Mixed (v : Fin 2 → ℝ) : Prop :=
  (0 < v 0 ∧ v 1 < 0) ∨ (v 0 < 0 ∧ 0 < v 1)

private theorem fixed_signed (A : Mat) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ i j, 0 ≤ A i j) (hd : A.det = 1 ∨ A.det = -1)
    (hf : A *ᵥ ![a,-b] = ![a,-b]) : A = 1 := by
  have h0 := congrFun hf 0
  have h1 := congrFun hf 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at h0 h1
  have hdet : a * A.det = a * A 1 1 + b * A 0 1 := by
    simp only [Matrix.det_fin_two]
    linear_combination A 1 1 * h0 - A 0 1 * h1
  have he : 1 ≤ A 1 1 := by nlinarith [hA 1 0]
  have hdetle : A.det ≤ 1 := by rcases hd with hd | hd <;> linarith
  have hu : A 0 1 = 0 := by nlinarith [hA 0 1]
  have heq : A 1 1 = 1 := by nlinarith
  have hg : A 1 0 = 0 := by rw [heq] at h1; nlinarith
  have hh : A 0 0 = 1 := by rw [hu] at h0; nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply,hh,hu,hg,heq]

/-- A mixed image never exceeds the initial positive or negative magnitude. -/
private theorem mixed_bounds (u : List Bool) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    let v := futureProduct u *ᵥ ![a,-b]
    Mixed v → ∀ i, -b ≤ v i ∧ v i ≤ a := by
  dsimp only
  have invariant : ∀ (u : List Bool) (v : Fin 2 → ℝ),
      ((∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0) ∨
        (∀ i, -b ≤ v i ∧ v i ≤ a)) →
      (∀ i, 0 ≤ (futureProduct u *ᵥ v) i) ∨
      (∀ i, (futureProduct u *ᵥ v) i ≤ 0) ∨
      (∀ i, -b ≤ (futureProduct u *ᵥ v) i ∧ (futureProduct u *ᵥ v) i ≤ a) := by
    intro u
    induction u with
    | nil => intro v hv; simpa [futureProduct] using hv
    | cons e u ih =>
      intro v hv
      simp only [futureProduct,← Matrix.mulVec_mulVec]
      apply ih
      cases e
      · simp only [Bool.false_eq_true, ↓reduceIte,atom_m]
        rcases hv with hp | hn | hm
        · left; intro i; fin_cases i <;> simp <;> linarith [hp 0,hp 1]
        · right; left; intro i; fin_cases i <;> simp <;> linarith [hn 0,hn 1]
        · by_cases hp : 0 ≤ v 0 ∧ 0 ≤ v 1
          · left; intro i; fin_cases i <;> simp <;> linarith [hp.1,hp.2]
          · by_cases hn : v 0 ≤ 0 ∧ v 1 ≤ 0
            · right; left; intro i; fin_cases i <;> simp <;> linarith [hn.1,hn.2]
            · right; right
              intro i
              fin_cases i
              · simpa using hm 1
              · simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
                rcases hm 0 with ⟨h00,h01⟩
                rcases hm 1 with ⟨h10,h11⟩
                constructor <;> rcases le_total (v 0) 0 with h | h <;>
                  rcases le_total (v 1) 0 with h' | h' <;> first | linarith | exact (hp ⟨h,h'⟩).elim | exact (hn ⟨h,h'⟩).elim
      · simp only [↓reduceIte,atom_j]
        rcases hv with hp | hn | hm
        · left; intro i; fin_cases i <;> simpa using hp _
        · right; left; intro i; fin_cases i <;> simpa using hn _
        · right; right; intro i; fin_cases i <;> simpa using hm _
  have hv := invariant u ![a,-b] (Or.inr (Or.inr (by
    intro i; fin_cases i <;> simp <;> linarith)))
  intro hm
  rcases hv with hp | hn | hbound
  · rcases hm with hm | hm <;> linarith [hp 0,hp 1]
  · rcases hm with hm | hm <;> linarith [hn 0,hn 1]
  · exact hbound

/-- Any actual word whose mixed signed image has the original positive level
has identity matrix, including empty and nonempty identity words. -/
theorem mixed_level_identity (u : List Bool) (p : PrimitiveCoordinates)
    (ha : 0 < p.a) (hb : 0 < p.b) (hc : 0 < p.c) (hd : 0 < p.d)
    (hmixed : Mixed (futureProduct u *ᵥ p.column))
    (hlevel : (p.c:ℝ)*(futureProduct u *ᵥ p.column) 0 -
      (p.d:ℝ)*(futureProduct u *ᵥ p.column) 1 = (p.a:ℝ)*p.c+(p.b:ℝ)*p.d) :
    futureProduct u = 1 := by
  have ha' : (0:ℝ) < p.a := by exact_mod_cast ha
  have hb' : (0:ℝ) < p.b := by exact_mod_cast hb
  have hc' : (0:ℝ) < p.c := by exact_mod_cast hc
  have hd' : (0:ℝ) < p.d := by exact_mod_cast hd
  have hbound := mixed_bounds u p.a p.b ha' hb' hmixed
  change ∀ i, -(p.b:ℝ) ≤ (futureProduct u *ᵥ p.column) i ∧
    (futureProduct u *ᵥ p.column) i ≤ p.a at hbound
  have hfix : futureProduct u *ᵥ p.column = p.column := by
    rcases hmixed with hm | hm
    · have h0 := (hbound 0).2
      have h1 := (hbound 1).1
      have he0 : (futureProduct u *ᵥ p.column) 0 = p.a := by nlinarith
      have he1 : (futureProduct u *ᵥ p.column) 1 = -(p.b:ℝ) := by nlinarith
      ext i; fin_cases i
      · exact he0
      · exact he1
    · nlinarith [mul_pos hc' ha',mul_pos hd' hb']
  have hlegal := (legal_matrix_monoid (futureProduct u)).mp ⟨u,rfl⟩
  exact fixed_signed (futureProduct u) p.a p.b ha' hb' (fun i j => (hlegal.1 i j).1)
    hlegal.2 hfix

private def Primitive (v : Fin 2 → ℝ) : Prop :=
  ∃ x y : ℤ, v 0 = (x:ℝ) ∧ v 1 = (y:ℝ) ∧ IsCoprime x y

private theorem word_primitive (u : List Bool) (v : Fin 2 → ℝ) (hv : Primitive v) :
    Primitive (futureProduct u *ᵥ v) := by
  induction u generalizing v with
  | nil => simpa [futureProduct] using hv
  | cons e u ih =>
    simp only [futureProduct,← Matrix.mulVec_mulVec]
    apply ih
    obtain ⟨x,y,hx,hy,hcop⟩ := hv
    cases e
    · simp only [Bool.false_eq_true,↓reduceIte,atom_m]
      refine ⟨y,x+y,by simpa using hy,?_,?_⟩
      · simp [hx,hy]
      · simpa using hcop.symm.mul_add_left_right 1
    · simp only [↓reduceIte,atom_j]
      exact ⟨y,x,hy,hx,hcop.symm⟩

private theorem column_primitive (p : PrimitiveCoordinates) : Primitive p.column := by
  exact ⟨p.a,-(p.b:ℤ),rfl,by simp [PrimitiveCoordinates.column],
    p.column_primitive.isCoprime.neg_right⟩

private theorem unit_coordinate (v : Fin 2 → ℝ) (hv : Primitive v) :
    (v 0 = 0 → v 1 = 1 ∨ v 1 = -1) ∧
    (v 1 = 0 → v 0 = 1 ∨ v 0 = -1) ∧
    (v 0 = v 1 → v 0 = 1 ∨ v 0 = -1) := by
  obtain ⟨x,y,hx,hy,hcop⟩ := hv
  have unit (z : ℤ) (hz : IsUnit z) : (z:ℝ) = 1 ∨ (z:ℝ) = -1 := by
    rcases Int.isUnit_iff.mp hz with hz | hz <;> simp [hz]
  refine ⟨?_,?_,?_⟩
  · intro h
    have hx0 : x = 0 := by exact_mod_cast (hx.symm.trans h)
    rw [hx0,isCoprime_zero_left] at hcop
    rw [hy]
    exact unit y hcop
  · intro h
    have hy0 : y = 0 := by exact_mod_cast (hy.symm.trans h)
    rw [hy0,isCoprime_zero_right] at hcop
    rw [hx]
    exact unit x hcop
  · intro h
    have hxy : x = y := by exact_mod_cast (hx.symm.trans (h.trans hy))
    rw [← hxy,isCoprime_self] at hcop
    rw [hx]
    exact unit x hcop

private theorem level_large (p : PrimitiveCoordinates)
    (ha : 0 < p.a) (hb : 0 < p.b) (hc : 0 < p.c) (hd : 0 < p.d) :
    (p.c:ℝ) < (p.a:ℝ)*p.c+(p.b:ℝ)*p.d ∧
    (p.d:ℝ) < (p.a:ℝ)*p.c+(p.b:ℝ)*p.d := by
  have ha' : (1:ℝ) ≤ p.a := by exact_mod_cast ha
  have hb' : (1:ℝ) ≤ p.b := by exact_mod_cast hb
  have hc' : (0:ℝ) < p.c := by exact_mod_cast hc
  have hd' : (0:ℝ) < p.d := by exact_mod_cast hd
  constructor <;> nlinarith

private theorem level_interior (u : List Bool) (p : PrimitiveCoordinates)
    (ha : 0 < p.a) (hb : 0 < p.b) (hc : 0 < p.c) (hd : 0 < p.d)
    (hne : futureProduct u ≠ 1)
    (hl : (p.c:ℝ)*(futureProduct u *ᵥ p.column) 0 -
      (p.d:ℝ)*(futureProduct u *ᵥ p.column) 1 = (p.a:ℝ)*p.c+(p.b:ℝ)*p.d) :
    Positive (futureProduct u *ᵥ p.column) ∨ Negative (futureProduct u *ᵥ p.column) := by
  let v := futureProduct u *ᵥ p.column
  have hunit := unit_coordinate v (word_primitive u p.column (column_primitive p))
  obtain ⟨htc,htd⟩ := level_large p ha hb hc hd
  have hc' : (0:ℝ) < p.c := by exact_mod_cast hc
  have hd' : (0:ℝ) < p.d := by exact_mod_cast hd
  have h0 : v 0 ≠ 0 := by
    intro h
    rcases hunit.1 h with hh | hh <;> change v 1 = _ at hh <;>
      change (p.c:ℝ)*v 0 - (p.d:ℝ)*v 1 = _ at hl <;> rw [h,hh] at hl <;> nlinarith
  have h1 : v 1 ≠ 0 := by
    intro h
    rcases hunit.2.1 h with hh | hh <;> change v 0 = _ at hh <;>
      change (p.c:ℝ)*v 0 - (p.d:ℝ)*v 1 = _ at hl <;> rw [h,hh] at hl <;> nlinarith
  have hmix : ¬ Mixed v := fun hm => hne (mixed_level_identity u p ha hb hc hd hm hl)
  rcases lt_or_gt_of_ne h0 with hn0 | hp0 <;>
    rcases lt_or_gt_of_ne h1 with hn1 | hp1
  · exact Or.inr ⟨hn0,hn1⟩
  · exact (hmix (Or.inr ⟨hn0,hp1⟩)).elim
  · exact (hmix (Or.inl ⟨hp0,hn1⟩)).elim
  · exact Or.inl ⟨hp0,hp1⟩

private theorem positive_sum (u : List Bool) (v : Fin 2 → ℝ) (hv : Positive v) :
    Positive (futureProduct u *ᵥ v) ∧
    v 0+v 1 ≤ (futureProduct u *ᵥ v) 0+(futureProduct u *ᵥ v) 1 ∧
    (v 0+v 1 = (futureProduct u *ᵥ v) 0+(futureProduct u *ᵥ v) 1 →
      futureProduct u = 1 ∨ futureProduct u = actionJ) := by
  induction u generalizing v with
  | nil => simp [futureProduct,hv]
  | cons e u ih =>
    cases e
    · have hw : Positive (actionM *ᵥ v) := by
        rw [atom_m]; exact ⟨hv.2,add_pos hv.1 hv.2⟩
      obtain ⟨hp,hs,he⟩ := ih _ hw
      simp only [futureProduct,Bool.false_eq_true,↓reduceIte,← Matrix.mulVec_mulVec]
      refine ⟨hp,?_,?_⟩
      · rw [atom_m] at hs
        dsimp at hs
        linarith [hv.2]
      · intro h
        rw [atom_m] at hs
        dsimp at hs
        linarith [hv.2]
    · have hw : Positive (actionJ *ᵥ v) := by rw [atom_j]; exact ⟨hv.2,hv.1⟩
      obtain ⟨hp,hs,he⟩ := ih _ hw
      simp only [futureProduct,↓reduceIte,← Matrix.mulVec_mulVec]
      refine ⟨hp,?_,?_⟩
      · rw [atom_j] at hs
        dsimp at hs
        linarith
      · intro h
        have heq : (actionJ *ᵥ v) 0+(actionJ *ᵥ v) 1 =
            (futureProduct u *ᵥ actionJ *ᵥ v) 0+(futureProduct u *ᵥ actionJ *ᵥ v) 1 := by
          rw [atom_j]; dsimp; linarith
        rcases he heq with hu | hu
        · right; rw [hu,Matrix.one_mul]
        · left; rw [hu,j_square]

private theorem endpoint_injective (w : Fin 3 → List Bool) (N : Mat)
    (h : OrientedKernelGenerator w N) : Function.Injective (prefixMatrix w) := by
  have hsur := (kernel_signs_positive_trace_invertible w N h).2.2.2
  intro i j hij
  by_contra hne
  obtain ⟨X,hX⟩ := hsur (fun k => if k = i then 1 else 0)
  have hi := congrFun hX i
  have hj := congrFun hX j
  change Matrix.trace (prefixMatrix w i * X) = _ at hi
  change Matrix.trace (prefixMatrix w j * X) = _ at hj
  rw [hij] at hi
  simp [hne,Ne.symm hne] at hi hj
  linarith

private theorem prefix_step (w : Fin 3 → List Bool) (i : Fin 3) :
    prefixMatrix w i.succ = futureProduct (w i) * prefixMatrix w i.castSucc := by
  fin_cases i <;>
    simp [prefixMatrix,prefixWord,List.ofFn_succ,product_append,futureProduct]

private theorem level_of_parameter (p : PrimitiveCoordinates) (A : Mat) (m : ℤ)
    (hm : A *ᵥ p.column = p.column+(m:ℝ) • p.direction) :
    (p.c:ℝ)*(A *ᵥ p.column) 0 - (p.d:ℝ)*(A *ᵥ p.column) 1 =
      (p.a:ℝ)*p.c+(p.b:ℝ)*p.d := by
  rw [hm]
  simp [PrimitiveCoordinates.column,PrimitiveCoordinates.direction]
  ring

end D5.S3.Observer.CubicGain.PhaseRigidity
