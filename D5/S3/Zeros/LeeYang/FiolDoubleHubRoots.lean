/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubRoots
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubRoots
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub roots identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubSamples
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
namespace FiolDoubleHub
theorem corrected_samples (d : ℕ) (hd : 2≤d) :
    ∃ s : ℕ → ℝ, s 0=0 ∧ s (N d)=Real.pi ∧
      (∀ k, k<N d → s k<s (k+1)) ∧
      (∀ k, k≤N d → 0<(-1:ℝ)^k*(phaseValue d (s k)).re) := by
  have hn : 4≤N d := by
    by_cases ho : Odd d <;> simp only [N,ho,ite_true,ite_false]
    · rw [Nat.odd_iff] at ho; omega
    · omega
  have hm : 0<N d/2 ∧ N d/2+1<N d := by omega
  by_cases hi : d%4=2
  · obtain ⟨he,l,r,hl,hlr,hr,hfl,hfr⟩ := central_replace_data d hd hi
    refine ⟨replaceSample (baseSample d) (N d/2) l r,?_,?_,?_,?_⟩
    · simp only [replaceSample,hm.1,ite_true,baseSample,ite_true]
    · simpa only [replaceSample,show ¬N d<N d/2 by omega,show N d≠N d/2 by omega,
        show N d≠N d/2+1 by omega,ite_false] using baseSample_last d hd
    · intro k hk
      exact replaceSample_succ _ _ _ _ _ hm (fun k hk => baseSample_succ d k hd hk) ⟨hl,hlr,hr⟩ k hk
    · intro k hk
      apply replaceSample_signed (fun x => (phaseValue d x).re) (baseSample d) (N d) (N d/2) l r hm he _ hfl hfr k hk
      intro j hj hjm
      exact baseSample_signed d j hd hj (by omega)
  · obtain ⟨c,hcl,hcr,hfc⟩ := central_insert_data d hd hi
    refine ⟨insertSample (baseSample d) (N d/2) c,?_,?_,?_,?_⟩
    · simp only [insertSample,hm.1,ite_true,baseSample,ite_true]
    · simpa only [insertSample,show ¬N d<N d/2 by omega,show N d≠N d/2 by omega,
        ite_false] using baseSample_last d hd
    · intro k hk
      exact insertSample_succ _ _ _ _ ⟨hm.1,by omega⟩ (fun k hk => baseSample_succ d k hd hk) ⟨hcl,hcr⟩ k hk
    · intro k hk
      apply insertSample_signed (fun x => (phaseValue d x).re) (baseSample d) (N d) (N d/2) c ⟨hm.1,by omega⟩ _ hfc k hk
      intro j hj
      exact baseSample_signed d j hd hj (by omega)

private theorem all_upper_roots (d : ℕ) (hd : 2≤d) :
    ∃ theta : Fin (N d) → ℝ, StrictMono theta ∧
      (∀ j, 0<theta j ∧ theta j<Real.pi ∧
        ((Q d).map Complex.ofRealHom).IsRoot (Complex.exp ((theta j:ℂ)*Complex.I))) := by
  obtain ⟨s,hs0,hsn,hstep,hsign⟩ := corrected_samples d hd
  have hmono : StrictMono (fun j : Fin (N d+1) => s j) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    exact hstep j j.isLt
  have hbound : ∀ j : Fin (N d+1), 0≤s j ∧ s j≤Real.pi := by
    intro j
    have hl := hmono.monotone (Fin.zero_le j)
    have hr := hmono.monotone (Fin.le_last j)
    simpa only [Fin.val_zero,Fin.val_last,hs0,hsn] using And.intro hl hr
  have hprod : ∀ j : Fin (N d),
      (phaseValue d (s j.castSucc)).re*(phaseValue d (s j.succ)).re<0 := by
    intro j
    exact signed_succ_product (fun x => (phaseValue d x).re) s j
      (hsign j (by omega)) (hsign (j+1) (by omega))
  obtain ⟨theta,_,hm,hr⟩ := roots_from_alternating_samples d (N d) hd _ hmono hbound hprod
  exact ⟨theta,hm,hr⟩

theorem Q_complete_roots (d : ℕ) (hd : 2≤d) :
    ∃ theta : Fin (N d) → ℝ, StrictMono theta ∧
      (∀ j, 0<theta j ∧ theta j<Real.pi) ∧
      ((Q d).map Complex.ofRealHom).roots =
        Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +
        Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧
      ((Q d).map Complex.ofRealHom).roots.Nodup := by
  classical
  obtain ⟨theta,hm,hr⟩ := all_upper_roots d hd
  let z := fun j => Complex.exp ((theta j:ℂ)*Complex.I)
  have hz : Function.Injective z := by
    intro j k he
    apply hm.injective
    exact exp_upper_injective ⟨(hr j).1.le,(hr j).2.1.le⟩
      ⟨(hr k).1.le,(hr k).2.1.le⟩ he
  have hupper : ∀j,0<(z j).im := by
    intro j
    simp only [z,Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (hr j).1 (hr j).2.1
  obtain ⟨hdeg,_,_,_,hne⟩ := candidate_degree_reciprocity d hd
  obtain ⟨he,hn⟩ := roots_exhausted_by_upper_family (Q d) (N d) hne hdeg.le z hz hupper (fun j => (hr j).2.2)
  exact ⟨theta,hm,fun j => ⟨(hr j).1,(hr j).2.1⟩,he,hn⟩

end FiolDoubleHub

namespace FiolDoubleHub
private theorem candidate_factorization (m : ℕ) (hm : 1≤m) :
    (R m).map Complex.ofRealHom =
      (Polynomial.X-Polynomial.C (1:ℂ))^h (m+1)*(Q (m+1)).map Complex.ofRealHom := by
  have he : Even (h (m+1)) := by
    unfold h
    split_ifs
    · exact even_two_mul _
    · exact ⟨m,by omega⟩
  have hfac : (1-Polynomial.X : Polynomial ℂ)^h (m+1)=
      (Polynomial.X-Polynomial.C (1:ℂ))^h (m+1) := by
    rw [show (1-Polynomial.X : Polynomial ℂ)=-(Polynomial.X-Polynomial.C 1) by simp only [Polynomial.C_1]; ring]
    exact he.neg_pow _
  simp only [R,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_X,hfac]

theorem candidate_full_root_multiset (m : ℕ) (hm : 1≤m) :
    ∃ theta : Fin (N (m+1)) → ℝ, StrictMono theta ∧
      (∀j,0<theta j ∧ theta j<Real.pi) ∧
      ((R m).map Complex.ofRealHom).roots =
        Multiset.replicate (h (m+1)) 1 +
        Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +
        Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧
      ((Q (m+1)).map Complex.ofRealHom).roots.Nodup := by
  classical
  obtain ⟨theta,ht,hb,he,hn⟩ := Q_complete_roots (m+1) (by omega)
  refine ⟨theta,ht,hb,?_,hn⟩
  have hp : (R m).map Complex.ofRealHom≠0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr (candidate_R_structure m hm).2.2.2.2
  rw [candidate_factorization m hm] at hp ⊢
  rw [Polynomial.roots_mul hp,Polynomial.roots_pow,Polynomial.roots_X_sub_C,he]
  simp only [Multiset.nsmul_singleton,add_assoc]

private theorem Q_roots_norm_one (d : ℕ) (hd : 2≤d) (z : ℂ)
    (hz : ((Q d).map Complex.ofRealHom).IsRoot z) : ‖z‖=1 := by
  classical
  obtain ⟨theta,_,_,he,_⟩ := Q_complete_roots d hd
  have hne : (Q d).map Complex.ofRealHom≠0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr (candidate_degree_reciprocity d hd).2.2.2.2
  have hzmem := (Polynomial.mem_roots hne).mpr hz
  rw [he] at hzmem
  rcases Multiset.mem_add.mp hzmem with hu | hl
  · obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hu
    rw [Complex.norm_exp]
    simp
  · obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hl
    rw [norm_star,Complex.norm_exp]
    simp

private theorem Q_root_simple (d : ℕ) (hd : 2≤d) (z : ℂ)
    (hz : ((Q d).map Complex.ofRealHom).IsRoot z) :
    Polynomial.rootMultiplicity z ((Q d).map Complex.ofRealHom)=1 := by
  classical
  obtain ⟨_,_,_,_,hn⟩ := Q_complete_roots d hd
  have hne : (Q d).map Complex.ofRealHom≠0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr (candidate_degree_reciprocity d hd).2.2.2.2
  rw [←Polynomial.count_roots]
  exact Multiset.count_eq_one_of_mem hn ((Polynomial.mem_roots hne).mpr hz)

theorem candidate_nonunit_root_multiplicity (m : ℕ) (hm : 1≤m) (z : ℂ)
    (hz : ((R m).map Complex.ofRealHom).IsRoot z) (hz1 : z≠1) :
    Polynomial.rootMultiplicity z ((R m).map Complex.ofRealHom)=1 ∧ ‖z‖=1 := by
  have hfac : ¬((Polynomial.X-Polynomial.C (1:ℂ))^h (m+1)).IsRoot z := by
    simp only [Polynomial.IsRoot,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr hz1)
  have hp : (R m).map Complex.ofRealHom≠0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr (candidate_R_structure m hm).2.2.2.2
  have hq : ((Q (m+1)).map Complex.ofRealHom).IsRoot z := by
    rw [candidate_factorization m hm,Polynomial.IsRoot,Polynomial.eval_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hfac
  constructor
  · rw [candidate_factorization m hm] at hp ⊢
    rw [Polynomial.rootMultiplicity_mul hp,Polynomial.rootMultiplicity_eq_zero hfac,zero_add]
    exact Q_root_simple (m+1) (by omega) z hq
  · exact Q_roots_norm_one (m+1) (by omega) z hq

theorem candidate_other_roots_card (m : ℕ) (hm : 1≤m) :
    (((R m).map Complex.ofRealHom).roots.filter (fun z => z≠1)).card =
      if Even m then 2*m+4 else 2*m+6 := by
  classical
  obtain ⟨theta,_,hb,he,_⟩ := candidate_full_root_multiset m hm
  have hupper : ∀ j, Complex.exp ((theta j:ℂ)*Complex.I)≠1 := by
    intro j hj
    have hh := congrArg Complex.im hj
    simp only [Complex.exp_ofReal_mul_I_im,Complex.one_im] at hh
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (hb j).1 (hb j).2) hh
  have hlower : ∀ j, star (Complex.exp ((theta j:ℂ)*Complex.I))≠1 := by
    intro j hj
    apply hupper j
    simpa only [star_star,star_one] using congrArg star hj
  have hfu : (Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I))).filter (fun z => z≠1)=
      Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) := by
    apply Multiset.filter_eq_self.mpr
    intro z hz
    obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hz
    exact hupper j
  have hfl : (Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I)))).filter (fun z => z≠1)=
      Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) := by
    apply Multiset.filter_eq_self.mpr
    intro z hz
    obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hz
    exact hlower j
  have hf0 : (Multiset.replicate (h (m+1)) (1:ℂ)).filter (fun z => z≠1)=0 := by
    apply Multiset.filter_eq_nil.mpr
    intro z hz
    exact not_not_intro (Multiset.mem_replicate.mp hz).2
  rw [he,Multiset.filter_add,Multiset.filter_add,hfu,hfl,hf0,Multiset.zero_add]
  simp only [
    Multiset.card_add,Multiset.card_map,Finset.card_val,Finset.card_univ,Fintype.card_fin]
  by_cases hpar : Even m
  · have ho : Odd (m+1) := hpar.add_odd (by decide : Odd 1)
    simp only [hpar,ite_true,N,ho]
    omega
  · have ho : ¬Odd (m+1) := by rw [Nat.odd_iff,Nat.even_iff] at *; omega
    simp only [hpar,ite_false,N,ho]
    omega

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
