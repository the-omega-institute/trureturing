/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubPhysical
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: Complete roots and multiplicities of the actual physical coefficient. -/

import D5.S3.Zeros.LeeYang.FiolDoubleHubRoots

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.LeeYang.FiolDoubleHub

private theorem spin_vertex {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V) (M : V → ℕ) :
    (∑ st : V → Bool,
      Polynomial.C ((-1 : ℝ) ^ (Finset.univ.filter
        (fun e : E => st (src e) ≠ st (tgt e))).card) *
      Polynomial.X ^ (∑ v ∈ Finset.univ.filter (fun v : V => st v = true), M v)) =
    ∏ v : V, (1 + Polynomial.C ((-1 : ℝ) ^
      ((Finset.univ.filter (fun e : E => src e = v)).card +
       (Finset.univ.filter (fun e : E => tgt e = v)).card)) * Polynomial.X ^ M v) := by
  classical
  let deg (v : V) := (Finset.univ.filter (fun e : E => src e = v)).card +
    (Finset.univ.filter (fun e : E => tgt e = v)).card
  let f (v : V) (b : Bool) : Polynomial ℝ :=
    if b = true then Polynomial.C ((-1 : ℝ)^deg v) * Polynomial.X^M v else 1
  have hterm (st : V → Bool) :
      Polynomial.C ((-1 : ℝ) ^ (Finset.univ.filter
        (fun e : E => st (src e) ≠ st (tgt e))).card) *
      Polynomial.X ^ (∑ v ∈ Finset.univ.filter (fun v : V => st v = true), M v) =
        ∏ v : V, f v (st v) := by
    let sgn (v : V) : Polynomial ℝ := if st v = true then -1 else 1
    have hsrc : (∏ e : E, sgn (src e)) =
        ∏ v : V, sgn v ^ (Finset.univ.filter (fun e : E => src e = v)).card := by
      simpa only [Finset.prod_const] using
        (Finset.prod_fiberwise' (Finset.univ : Finset E) src sgn).symm
    have htgt : (∏ e : E, sgn (tgt e)) =
        ∏ v : V, sgn v ^ (Finset.univ.filter (fun e : E => tgt e = v)).card := by
      simpa only [Finset.prod_const] using
        (Finset.prod_fiberwise' (Finset.univ : Finset E) tgt sgn).symm
    have hsign : Polynomial.C ((-1 : ℝ) ^ (Finset.univ.filter
        (fun e : E => st (src e) ≠ st (tgt e))).card) =
        ∏ v : V, (if st v = true then (-1 : Polynomial ℝ)^deg v else 1) := by
      calc
        _ = ∏ e : E, (if st (src e) ≠ st (tgt e) then (-1 : Polynomial ℝ) else 1) := by
          simpa using (Finset.prod_filter (s := (Finset.univ : Finset E))
            (fun e : E => st (src e) ≠ st (tgt e)) (fun _ : E => (-1 : Polynomial ℝ)))
        _ = ∏ e : E, sgn (src e) * sgn (tgt e) := by
          apply Finset.prod_congr rfl
          intro e he
          cases hs : st (src e) <;> cases ht : st (tgt e) <;> simp [sgn, hs, ht]
        _ = (∏ e : E, sgn (src e)) * ∏ e : E, sgn (tgt e) := Finset.prod_mul_distrib
        _ = (∏ v : V, sgn v ^ (Finset.univ.filter (fun e : E => src e = v)).card) *
              ∏ v : V, sgn v ^ (Finset.univ.filter (fun e : E => tgt e = v)).card := by
          rw [hsrc, htgt]
        _ = ∏ v : V, (if st v = true then (-1 : Polynomial ℝ)^deg v else 1) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro v hv
          cases hs : st v <;> simp [sgn, deg, hs, pow_add]
    have hmon : (Polynomial.X : Polynomial ℝ) ^
        (∑ v ∈ Finset.univ.filter (fun v : V => st v = true), M v) =
        ∏ v : V, if st v = true then Polynomial.X ^ M v else 1 := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_filter (fun v : V => st v = true) _
    rw [hsign, hmon, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    cases hs : st v <;> simp [f]
  calc
    _ = ∑ st : V → Bool, ∏ v : V, f v (st v) := Finset.sum_congr rfl (fun st _ => hterm st)
    _ = ∏ v : V, (f v true + f v false) := by
      simpa only [Fintype.sum_bool] using (Fintype.prod_sum f).symm
    _ = _ := by simp [f, deg, add_comm]

private theorem source_spin_vertex (m : ℕ) (n : Edge m → ℕ) :
    allSpinSource n = allVertexSource n := by
  unfold allSpinSource allVertexSource
    D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.treePoly
  apply Finset.sum_congr rfl
  intro k hk
  unfold splitSource
  congr 1
  exact spin_vertex src tgt (mass n k)

/-- The independent formal truncation retaining every spin state. -/
noncomputable def spinTruncation (m cutoff : ℕ) :
    MvPolynomial ℕ (Polynomial ℝ) :=
  ∑ n ∈ Fintype.piFinset (fun _ : Edge m => Finset.Icc 2 cutoff),
    MvPolynomial.C (Polynomial.C (sourcePrefactor n) * allSpinSource n) *
      ∏ e : Edge m, MvPolynomial.X (2*n e-1)

noncomputable def spinCoefficient (m cutoff : ℕ) : Polynomial ℝ :=
  (spinTruncation m cutoff).coeff (targetMonomial m)

set_option maxHeartbeats 1000000 in
/-- The spin sum gives exactly the all-vertex formal coefficient. -/
theorem spin_coefficient_eq_source (m cutoff : ℕ) :
    spinCoefficient m cutoff = sourceCoefficient m cutoff := by
  unfold spinCoefficient spinTruncation sourceCoefficient sourceTruncation
  apply congrArg (fun p : MvPolynomial ℕ (Polynomial ℝ) => p.coeff (targetMonomial m))
  apply Finset.sum_congr rfl
  intro n hn
  rw [source_spin_vertex m n]


/- The coefficient is extracted from the all-vertex expression (2.19), labelled
   planarf2 in the source. The printed product index in (2.31) is distinct;
   this theorem makes no assertion about an author's intended correction. -/
theorem physical_root_classification (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :
    let p := (spinCoefficient m cutoff).map Complex.ofRealHom
    p.natDegree = 4*m+6 ∧ p ≠ 0 ∧
    ∃ theta : Fin (N (m+1)) → ℝ, StrictMono theta ∧
      (∀ j, 0 < theta j ∧ theta j < Real.pi) ∧
      p.roots = Multiset.replicate (h (m+1)) 1 +
        Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +
        Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧
      Polynomial.rootMultiplicity 1 p = (if Even m then 2*m+2 else 2*m) ∧
      (∀ z : ℂ, p.IsRoot z → z ≠ 1 →
        Polynomial.rootMultiplicity z p = 1 ∧ ‖z‖ = 1) ∧
      (p.roots.filter (fun z => z ≠ 1)).card = (if Even m then 2*m+4 else 2*m+6) ∧
      ¬ p.IsRoot (-1) ∧
      (p.IsRoot Complex.I ↔ m % 4 = 1) ∧
      (p.IsRoot (-Complex.I) ↔ m % 4 = 1) ∧
      (m % 4 = 1 → Polynomial.rootMultiplicity Complex.I p = 1 ∧
        Polynomial.rootMultiplicity (-Complex.I) p = 1) := by
  classical
  dsimp only
  rw [spin_coefficient_eq_source]
  let r := (R m).map Complex.ofRealHom
  let a : ℂ := (200*(12:ℝ)^(2*m):ℝ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hp : (sourceCoefficient m cutoff).map Complex.ofRealHom = Polynomial.C a*r := by
    rw [actual_coefficient_identity m cutoff hm hc,Polynomial.map_mul,Polynomial.map_C]
    rfl
  have hrne : r ≠ 0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr
      (candidate_R_structure m hm).2.2.2.2
  have hpne : (sourceCoefficient m cutoff).map Complex.ofRealHom ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr ha) hrne
  have hroots : ((sourceCoefficient m cutoff).map Complex.ofRealHom).roots = r.roots := by
    rw [hp,Polynomial.roots_C_mul r ha]
  have hmult (z : ℂ) :
      Polynomial.rootMultiplicity z ((sourceCoefficient m cutoff).map Complex.ofRealHom) =
        Polynomial.rootMultiplicity z r := by
    rw [←Polynomial.count_roots,hroots,Polynomial.count_roots]
  have hroot (z : ℂ) :
      ((sourceCoefficient m cutoff).map Complex.ofRealHom).IsRoot z ↔ r.IsRoot z := by
    rw [←Polynomial.mem_roots hpne,←Polynomial.mem_roots hrne,hroots]
  refine ⟨?_,hpne,?_⟩
  · rw [hp,Polynomial.natDegree_C_mul ha,
      Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective,
      (candidate_R_structure m hm).1]
  · obtain ⟨theta,ht,hb,he,_⟩ := candidate_full_root_multiset m hm
    refine ⟨theta,ht,hb,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact hroots.trans he
    · rw [hmult,candidate_one_multiplicity m hm]
      by_cases hmpar : Even m
      · have ho : Odd (m+1) := hmpar.add_odd (by decide : Odd 1)
        simp only [h,ho,hmpar,ite_true]
        omega
      · have ho : Odd m := Nat.not_even_iff_odd.mp hmpar
        have hn : ¬Odd (m+1) := Nat.not_odd_iff_even.mpr (ho.add_odd (by decide : Odd 1))
        simp only [h,hn,hmpar,ite_false]
        omega
    · intro z hz hz1
      rw [hmult]
      exact candidate_nonunit_root_multiplicity m hm z ((hroot z).mp hz) hz1
    · rw [hroots]
      exact candidate_other_roots_card m hm
    · intro hz
      have hr := (hroot (-1)).mp hz
      have hev : r.eval (-1) = Complex.ofReal ((R m).eval (-1:ℝ)) := by
        change ((R m).map Complex.ofRealHom).eval (-1) = _
        simpa using (Polynomial.eval_map_apply (p := R m) (f := Complex.ofRealHom) (-1:ℝ))
      have hn : Complex.ofReal ((R m).eval (-1:ℝ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (R_neg_one_pos m hm))
      exact hn (hev.symm.trans hr)
    · exact (hroot Complex.I).trans (candidate_I_iff m hm)
    · exact (hroot (-Complex.I)).trans (candidate_neg_I_iff m hm)
    · intro hi
      rw [hmult,hmult]
      exact ⟨candidate_I_simple m hm hi,candidate_neg_I_simple m hm hi⟩

end D5.S3.Zeros.LeeYang.FiolDoubleHub
