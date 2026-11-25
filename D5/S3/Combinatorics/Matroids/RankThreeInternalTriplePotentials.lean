/- GID: D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Mixed triples force a common cyclic additive term, constrained by the internal triples. -/

import D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers

namespace D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials

open Finset
open RankThreeOmissionPotentialFibers (IsThird potentialSpace third_value)
open RankThreeOmissionPotentials (covers IsOmissionPotential)

abbrev Row (d : ℕ) := Fin d → ZMod 3

/-- Every mixed pair has its product zero-sum completion. Every listed triple
is internal to a row or has zero product sum. -/
def LiftedLineFamily {d s : ℕ} {T : Type*} (points : T → Fin 3 → (Row d × ZMod s)) : Prop :=
  (∀ (x y : Row d) (a b : ZMod s), x ≠ y →
    IsThird points (x,a) (y,b) (-(x+y),-(a+b))) ∧
  ∀ t, (∀ j, (points t j).1 = (points t 0).1) ∨ (∑ j, points t j) = 0

/-- The internal observations that must vanish under the common cyclic map. -/
def InternalConstraints {d s : ℕ} {T : Type*} (points : T → Fin 3 → (Row d × ZMod s))
    (g : ZMod s →+ ZMod 3) : Prop :=
  (∀ x a b, (¬ ∃ t, covers (points t) (x,a) (x,b)) → g (a-b) = 0) ∧
  ∀ t, (∀ j, (points t j).1 = (points t 0).1) → g (∑ j, (points t j).2) = 0

private theorem common_additive_term {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (u v w : A → B) (hs : ∀ a b, u a + v b + w (-(a+b)) = 0) :
    ∃ g : A →+ B, (∀ a, u a = u 0 + g a) ∧ (∀ a, v a = v 0 + g a) := by
  let U (a : A) := u a - u 0
  let V (a : A) := v a - v 0
  let W (a : A) := w a - w 0
  have base : u 0 + v 0 + w 0 = 0 := by simpa using hs 0 0
  have norm (a b : A) : U a + V b + W (-(a+b)) = 0 := by
    calc
      _ = (u a + v b + w (-(a+b))) - (u 0 + v 0 + w 0) := by
        dsimp [U,V,W]
        abel
      _ = 0 := by rw [hs, base, sub_self]
  have first (a : A) : U a = -W (-a) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [V] using norm a 0
  have second (a : A) : V a = U a := by
    rw [first]
    apply eq_neg_of_add_eq_zero_left
    simpa [U] using norm 0 a
  let g : A →+ B :=
    { toFun := U, map_zero' := sub_self _, map_add' := fun a b => by
        calc
          U (a+b) = -W (-(a+b)) := first _
          _ = U a + V b := (eq_neg_of_add_eq_zero_left (norm a b)).symm
          _ = U a + U b := by rw [second] }
  refine ⟨g, fun a => ?_, fun a => ?_⟩
  · change u a = u 0 + U a
    dsimp [U]
    abel
  · change v a = v 0 + U a
    rw [← second]
    dsimp [V]
    abel

private theorem mixed_equations {d s : ℕ} {T : Type*} (points : T → Fin 3 → (Row d × ZMod s))
    (family : LiftedLineFamily points) (u : (Row d × ZMod s) → ZMod 3)
    (hs : ∀ t, (∑ j, u (points t j)) = 0) :
    ∀ (x y : Row d) (a b : ZMod s), x ≠ y →
      u (x,a) + u (y,b) + u (-(x+y),-(a+b)) = 0 :=
  by
    intro x y a b different
    rw [third_value points u hs (family.1 x y a b different), add_neg_cancel]

private theorem decompose_mixed {d s : ℕ} (hd : 0 < d) (u : (Row d × ZMod s) → ZMod 3)
    (anchor : u 0 = 0)
    (mixed : ∀ (x y : Row d) (a b : ZMod s), x ≠ y →
      u (x,a) + u (y,b) + u (-(x+y),-(a+b)) = 0) :
    ∃ (l : Row d →ₗ[ZMod 3] ZMod 3) (g : ZMod s →+ ZMod 3),
      ∀ p : (Row d × ZMod s), u p = l p.1 + g p.2 := by
  have across (x y : Row d) (hne : x ≠ y) :
      ∃ g : ZMod s →+ ZMod 3, (∀ a, u (x,a) = u (x,0) + g a) ∧
        (∀ a, u (y,a) = u (y,0) + g a) :=
    common_additive_term (fun a => u (x,a)) (fun a => u (y,a))
      (fun a => u (-(x+y),a)) (fun a b => mixed x y a b hne)
  let row : Row d := fun _ => 1
  have nonzero : 0 ≠ row := by
    intro h
    exact zero_ne_one (congrFun h ⟨0,hd⟩)
  obtain ⟨g,hg,_⟩ := across 0 row nonzero
  have rows (x : Row d) (a : ZMod s) : u (x,a) = u (x,0) + g a := by
    by_cases hx : x = 0
    · simpa [hx] using hg a
    · obtain ⟨g',zero_row,other_row⟩ := across 0 x (Ne.symm hx)
      have eq : g' a = g a := add_left_cancel ((zero_row a).symm.trans (hg a))
      rw [other_row, eq]
  let f (x : Row d) := u (x,0)
  have f0 : f 0 = 0 := anchor
  have neg_sum (x y : Row d) : f (-(x+y)) = -(f x + f y) := by
    by_cases same : x = y
    · subst y
      have hx : -(x+x) = x := by
        apply neg_eq_of_add_eq_zero_left
        simpa only [three_nsmul, add_assoc] using ZModModule.char_nsmul_eq_zero 3 x
      rw [hx]
      apply eq_neg_of_add_eq_zero_right
      simpa only [three_nsmul, add_assoc] using ZModModule.char_nsmul_eq_zero 3 (f x)
    · apply eq_neg_of_add_eq_zero_right
      simpa only [add_zero,neg_zero] using mixed x y 0 0 same
  have negated (x) : f (-x) = -f x := by simpa only [add_zero,f0] using neg_sum x 0
  let l : Row d →+ ZMod 3 :=
    { toFun := f, map_zero' := f0, map_add' := fun x y => by
        have h := neg_sum x y
        rw [negated, neg_inj] at h
        exact h }
  exact ⟨l.toZModLinearMap 3, g, fun p => rows p.1 p.2⟩

private def separatedValue {d s : ℕ} (l : Row d →ₗ[ZMod 3] ZMod 3)
    (g : ZMod s →+ ZMod 3) : (Row d × ZMod s) →+ ZMod 3 where
  toFun p := l p.1 + g p.2
  map_zero' := by simp
  map_add' p q := by
    change l (p.1 + q.1) + g (p.2 + q.2) = (l p.1 + g p.2) + (l q.1 + g q.2)
    rw [map_add, map_add]
    abel

private theorem sum_hom_zero {A : Type*} [Fintype A] [AddCommGroup A]
    (f : A →+ ZMod 3) : (∑ x, f x) = 0 := by
  classical
  let v : ZMod 3 := ∑ x, f x
  have hn := Equiv.sum_comp (Equiv.neg A) (fun x => f x)
  simp only [Equiv.neg_apply,map_neg,sum_neg_distrib] at hn
  change -v = v at hn
  have twice : v + v = 0 := (congrArg (· + v) hn.symm).trans (neg_add_cancel v)
  have three : (v+v)+v = 0 := by
    simpa only [three_nsmul,add_assoc] using ZModModule.char_nsmul_eq_zero 3 v
  simpa only [twice,zero_add] using three

private theorem internal_sum {d s : ℕ} {T : Type*} (points : T → Fin 3 → (Row d × ZMod s))
    (l : Row d →ₗ[ZMod 3] ZMod 3) (g : ZMod s →+ ZMod 3) (t : T)
    (same : ∀ j, (points t j).1 = (points t 0).1) :
    (∑ j, separatedValue l g (points t j)) = g (∑ j, (points t j).2) := by
  change (∑ j, (l (points t j).1 + g (points t j).2)) = _
  rw [sum_add_distrib, ← map_sum g]
  have rowSum : (∑ j, l (points t j).1) = 0 := by
    simp_rw [same]
    rw [sum_const, card_univ, Fintype.card_fin]
    exact ZModModule.char_nsmul_eq_zero 3 _
  rw [rowSum, zero_add]

private theorem separated_isPotential {d s : ℕ} [NeZero s] {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (family : LiftedLineFamily points)
    (l : Row d →ₗ[ZMod 3] ZMod 3) (g : ZMod s →+ ZMod 3)
    (constraints : InternalConstraints points g) :
    IsOmissionPotential points 0 (separatedValue l g) := by
  refine ⟨map_zero _, sum_hom_zero _, fun _ => ZModModule.char_nsmul_eq_zero 3 _, ?_, ?_⟩
  · rintro ⟨x,a⟩ ⟨y,b⟩ missing
    have same : x = y := by
      by_contra h
      obtain ⟨t,i,j,_,_,_,_,hi,hj,_⟩ := family.1 x y a b h
      exact missing ⟨t,i,j,hi,hj⟩
    subst y
    have hg : g a = g b := sub_eq_zero.mp (by
      rw [← map_sub]
      exact constraints.1 x a b missing)
    change l x + g a = l x + g b
    rw [hg]
  · intro t
    have h : (∑ j, separatedValue l g (points t j)) = 0 := by
      rcases family.2 t with same | zero
      · exact (internal_sum points l g t same).trans (constraints.2 t same)
      · rw [← map_sum, zero, map_zero]
    simpa only [Fin.sum_univ_three] using h

/-- After adjoining internal triples, every normalized ternary potential splits
into a row functional and one additive map shared by the cyclic coordinates. -/
theorem potential_iff_separated {d s : ℕ} [NeZero s] {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (hd : 0 < d) (family : LiftedLineFamily points)
    (u : (Row d × ZMod s) → ZMod 3) :
    IsOmissionPotential points 0 u ↔
      ∃ (l : Row d →ₗ[ZMod 3] ZMod 3) (g : ZMod s →+ ZMod 3),
        InternalConstraints points g ∧ ∀ p : (Row d × ZMod s), u p = l p.1 + g p.2 := by
  constructor
  · intro hu
    have all (t : T) : (∑ j, u (points t j)) = 0 := by
      simpa only [Fin.sum_univ_three] using hu.2.2.2.2 t
    obtain ⟨l,g,h⟩ := decompose_mixed hd u hu.1 (mixed_equations points family u all)
    refine ⟨l,g,⟨?_,?_⟩,h⟩
    · intro x a b missing
      have he := hu.2.2.2.1 (x,a) (x,b) missing
      rw [h (x,a), h (x,b)] at he
      exact (map_sub g a b).trans (sub_eq_zero.mpr (add_left_cancel he))
    · intro t same
      have hf : (separatedValue l g : (Row d × ZMod s) → ZMod 3) = u :=
        funext (fun p => (h p).symm)
      rw [← internal_sum points l g t same, hf]
      exact all t
  · rintro ⟨l,g,hg,h⟩
    have hf : (separatedValue l g : (Row d × ZMod s) → ZMod 3) = u :=
      funext (fun p => (h p).symm)
    rw [← hf]
    exact separated_isPotential points family l g hg

/-- The residue map from the cyclic coordinate when it admits reduction modulo
three, and the zero map otherwise. -/
noncomputable def cyclicReduction (s : ℕ) : ZMod s →+ ZMod 3 := by
  classical
  exact if h : 3 ∣ s then (ZMod.castHom h (ZMod 3)).toAddMonoidHom else 0

/-- The extra cyclic coefficient is available exactly when all internal
constraints are compatible with reduction modulo three. -/
def AllowsExtra {d s : ℕ} {T : Type*} (points : T → Fin 3 → (Row d × ZMod s)) : Prop :=
  3 ∣ s ∧ InternalConstraints points (cyclicReduction s)

private def scaleCyclic {s : ℕ} (c : ZMod 3) (g : ZMod s →+ ZMod 3) :
    ZMod s →+ ZMod 3 where
  toFun a := c * g a
  map_zero' := by simp
  map_add' a b := by rw [map_add,mul_add]

private theorem cyclic_apply {s : ℕ} [NeZero s] (g : ZMod s →+ ZMod 3)
    (a : ZMod s) : g a = (a.val : ZMod 3) * g 1 := by
  have e : a.val • (1 : ZMod s) = a := by
    rw [nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val]
  simpa only [e,nsmul_eq_mul] using map_nsmul g a.val (1 : ZMod s)

private theorem cyclic_one_zero {s : ℕ} (g : ZMod s →+ ZMod 3) (h : ¬ 3 ∣ s) :
    g 1 = 0 := by
  have e : s • (1 : ZMod s) = 0 := by rw [nsmul_eq_mul,mul_one,ZMod.natCast_self]
  have hg := map_nsmul g s (1 : ZMod s)
  rw [e,map_zero,nsmul_eq_mul] at hg
  exact (mul_eq_zero.mp hg.symm).resolve_left (mt (ZMod.natCast_eq_zero_iff s 3).mp h)

private theorem cyclic_repr {s : ℕ} [NeZero s] (g : ZMod s →+ ZMod 3) :
    g = scaleCyclic (g 1) (cyclicReduction s) := by
  classical
  ext a
  change g a = g 1 * cyclicReduction s a
  by_cases h : 3 ∣ s
  · have hred : cyclicReduction s a = (a.val : ZMod 3) := by
      rw [cyclicReduction,dite_eq_left h]
      change ZMod.castHom h (ZMod 3) a = _
      calc
        _ = ZMod.castHom h (ZMod 3) (a.val : ZMod s) :=
          congrArg (ZMod.castHom h (ZMod 3)) (ZMod.natCast_zmod_val a).symm
        _ = _ := map_natCast _ _
    rw [cyclic_apply g a,hred,mul_comm]
  · rw [cyclic_apply g a,cyclic_one_zero g h]
    simp

private theorem reduction_one {s : ℕ} (h : 3 ∣ s) : cyclicReduction s 1 = 1 := by
  classical
  simp [cyclicReduction,h]

private noncomputable def coefficientSpace {d s : ℕ} {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) : Submodule (ZMod 3) (ZMod 3) := by
  classical
  exact if AllowsExtra points then ⊤ else ⊥

private theorem coefficient_zero {d s : ℕ} {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (closed : ¬ AllowsExtra points)
    (c : ZMod 3) (hc : c ∈ coefficientSpace points) : c = 0 := by
  classical
  unfold coefficientSpace at hc
  rw [ite_eq_right closed] at hc
  exact (Submodule.mem_bot (ZMod 3)).mp hc

private theorem coefficient_valid {d s : ℕ} [NeZero s] {T : Type*} (points : T → Fin 3 → (Row d × ZMod s))
    (g : ZMod s →+ ZMod 3) (hg : InternalConstraints points g) :
    g 1 ∈ coefficientSpace points := by
  classical
  by_cases hn : g 1 = 0
  · rw [hn]
    exact Submodule.zero_mem _
  have hdvd : 3 ∣ s := by
    by_contra h
    exact hn (cyclic_one_zero g h)
  have hred (a : ZMod s) : g a = g 1 * cyclicReduction s a :=
    DFunLike.congr_fun (cyclic_repr g) a
  have hall : AllowsExtra points := by
    refine ⟨hdvd,⟨?_,?_⟩⟩
    · intro x a b h
      exact (mul_eq_zero.mp ((hred _).symm.trans (hg.1 x a b h))).resolve_left hn
    · intro t same
      exact (mul_eq_zero.mp ((hred _).symm.trans (hg.2 t same))).resolve_left hn
  simp [coefficientSpace,hall]

private theorem coefficient_constraints {d s : ℕ} {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (c : coefficientSpace points) :
    InternalConstraints points (scaleCyclic c.val (cyclicReduction s)) := by
  classical
  have annihilates (a : ZMod s) (h : AllowsExtra points → cyclicReduction s a = 0) :
      c.val * cyclicReduction s a = 0 := by
    by_cases extra : AllowsExtra points
    · rw [h extra,mul_zero]
    · rw [coefficient_zero points extra c.val c.prop,zero_mul]
  exact ⟨fun x a b miss => annihilates _ (fun h => h.2.1 x a b miss),
    fun t same => annihilates _ (fun h => h.2.2 t same)⟩

private noncomputable def parameterMap {d s : ℕ} [NeZero s] {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (family : LiftedLineFamily points) :
    ((Row d →ₗ[ZMod 3] ZMod 3) × coefficientSpace points) →ₗ[ZMod 3]
      potentialSpace points 0 where
  toFun p :=
    ⟨separatedValue p.1 (scaleCyclic p.2.val (cyclicReduction s)),
      separated_isPotential points family p.1 _ (coefficient_constraints points p.2)⟩
  map_add' p q := by
    apply Subtype.ext
    funext x
    change (p.1 x.1 + q.1 x.1) + (p.2.val + q.2.val) * cyclicReduction s x.2 =
      (p.1 x.1 + p.2.val * cyclicReduction s x.2) +
      (q.1 x.1 + q.2.val * cyclicReduction s x.2)
    rw [add_mul]
    abel
  map_smul' c p := by
    apply Subtype.ext
    funext x
    change (c * p.1 x.1) + (c * p.2.val) * cyclicReduction s x.2 =
      c * (p.1 x.1 + p.2.val * cyclicReduction s x.2)
    rw [mul_add,mul_assoc]

private theorem parameterMap_bijective {d s : ℕ} [NeZero s] {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (hd : 0 < d) (family : LiftedLineFamily points) :
    Function.Bijective (parameterMap points family) := by
  classical
  constructor
  · intro p q h
    have equal (x : (Row d × ZMod s)) :
        p.1 x.1 + p.2.val * cyclicReduction s x.2 =
          q.1 x.1 + q.2.val * cyclicReduction s x.2 :=
      congrArg (fun v : potentialSpace points 0 => v.val x) h
    apply Prod.ext
    · apply LinearMap.ext
      intro x
      simpa using equal (x,0)
    · apply Subtype.ext
      by_cases extra : AllowsExtra points
      · simpa [reduction_one extra.1] using equal (0,1)
      · have hp := coefficient_zero points extra p.2.val p.2.prop
        have hq := coefficient_zero points extra q.2.val q.2.prop
        exact hp.trans hq.symm
  · intro u
    obtain ⟨l,g,hg,eq⟩ := (potential_iff_separated points hd family u.val).mp u.prop
    refine ⟨(l,⟨g 1,coefficient_valid points g hg⟩),Subtype.ext (funext fun x => ?_)⟩
    change separatedValue l (scaleCyclic (g 1) (cyclicReduction s)) x = u.val x
    rw [← cyclic_repr g]
    exact (eq x).symm

open Classical in
/-- The point-potential dimension increases by one exactly when the ordinary
mod-three residue of the cyclic coordinate satisfies every internal constraint. -/
theorem potential_finrank_internal_triples {d s : ℕ} [NeZero s] {T : Type*}
    (points : T → Fin 3 → (Row d × ZMod s)) (hd : 0 < d) (family : LiftedLineFamily points) :
    Module.finrank (ZMod 3) (potentialSpace points 0) =
      if AllowsExtra points then d + 1 else d := by
  classical
  rw [← (LinearEquiv.ofBijective (parameterMap points family)
    (parameterMap_bijective points hd family)).finrank_eq, Module.finrank_prod]
  have row : Module.finrank (ZMod 3) (Row d →ₗ[ZMod 3] ZMod 3) = d := by
    change Module.finrank (ZMod 3) (Module.Dual (ZMod 3) (Row d)) = d
    rw [Subspace.dual_finrank_eq,Module.finrank_pi,Fintype.card_fin]
  rw [row]
  by_cases extra : AllowsExtra points
  · have hs : coefficientSpace points = (⊤ : Submodule (ZMod 3) (ZMod 3)) := by
      unfold coefficientSpace
      rw [ite_eq_left extra]
    rw [hs,finrank_top,Module.finrank_self,ite_eq_left extra]
  · have hs : coefficientSpace points = (⊥ : Submodule (ZMod 3) (ZMod 3)) := by
      unfold coefficientSpace
      rw [ite_eq_right extra]
    rw [hs,finrank_bot,add_zero,ite_eq_right extra]

end D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials
