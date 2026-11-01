/- GID: D5/S3/Quantum/Fermionic/BcGhostJacobi
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostJacobi
   mirror-E: none(waiver:algebraic-ghost-witt-jacobi)
   anchors: []
   utility: none
   digest: Statewise finite triple-c expansion and Witt-Jacobi cancellation. -/

import D5.S3.Quantum.Fermionic.BcGhostBRST

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open private c_ket_tail c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

private theorem ccc_cycle (a b d : ℤ) : c a*c b*c d = c b*c d*c a := by
  calc
    _ = -(c b*c a)*c d := by rw [c_swap a b]
    _ = c b*c d*c a := by rw [neg_mul, mul_assoc, c_swap a d]; simp [mul_assoc]

private theorem ccc_ket_finite (r : ℤ) (S : Finset ℕ) :
    Function.HasFiniteSupport (fun ab : ℤ × ℤ => (c ab.1*c ab.2*c (r-ab.1-ab.2)) (ket S)) := by
  let A : ℤ := (S.sup id + 3 : ℕ)
  apply ((Set.finite_Icc (r-2*A) A).prod (Set.finite_Icc (r-2*A) A)).subset
  intro ab hab
  change (c ab.1*c ab.2*c (r-ab.1-ab.2)) (ket S) ≠ 0 at hab
  have ha : ab.1 ≤ A := by
    by_contra hn
    have hz : c ab.1 (ket S) = 0 := c_ket_tail _ S (by dsimp [A] at hn; omega)
    exact hab (by rw [ccc_cycle]; simp [Module.End.mul_apply, hz])
  have hb : ab.2 ≤ A := by
    by_contra hn
    have hz : c ab.2 (ket S) = 0 := c_ket_tail _ S (by dsimp [A] at hn; omega)
    exact hab (by rw [ccc_cycle, ccc_cycle]; simp [Module.End.mul_apply, hz])
  have hd : r-ab.1-ab.2 ≤ A := by
    by_contra hn
    have hz : c (r-ab.1-ab.2) (ket S) = 0 := c_ket_tail _ S (by dsimp [A] at hn; omega)
    exact hab (by simp [Module.End.mul_apply, hz])
  exact ⟨⟨by omega, ha⟩, by omega, hb⟩

private theorem ccc_finite (r : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun ab : ℤ × ℤ => (c ab.1*c ab.2*c (r-ab.1-ab.2)) v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [Function.HasFiniteSupport, Function.support]
  | add f g hf hg =>
    apply (hf.union hg).subset
    intro ab hab
    by_contra hn
    have hfz : (c ab.1*c ab.2*c (r-ab.1-ab.2)) f = 0 := by
      by_contra hz
      exact hn (Or.inl hz)
    have hgz : (c ab.1*c ab.2*c (r-ab.1-ab.2)) g = 0 := by
      by_contra hz
      exact hn (Or.inr hz)
    exact hab (by simp only [map_add, hfz, hgz, add_zero])
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs]
    simp only [map_smul]
    exact (ccc_ket_finite r S).fun_comp (smul_zero a)

private def cycle (r : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun ab := (ab.2, r-ab.1-ab.2)
  invFun ab := (r-ab.1-ab.2, ab.1)
  left_inv ab := by ext <;> dsimp <;> omega
  right_inv ab := by ext <;> dsimp <;> omega

private def splitPair : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun pa := (pa.2, pa.1-pa.2)
  invFun ab := (ab.1+ab.2, ab.1)
  left_inv pa := by ext <;> dsimp <;> omega
  right_inv ab := by ext <;> dsimp <;> omega

private def jacobiTerm (r : ℤ) (ab : ℤ × ℤ) : Module.End ℂ Fock :=
  ((1/4 : ℂ) * ((2*(ab.1+ab.2)-r : ℤ) : ℂ) * ((ab.1-ab.2 : ℤ) : ℂ)) •
    (c ab.1*c ab.2*c (r-ab.1-ab.2))

private theorem jacobiTerm_finite (r : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun ab : ℤ × ℤ => jacobiTerm r ab v) := by
  apply (ccc_finite r v).subset
  intro ab hab hn
  exact hab (by simp [jacobiTerm, hn])

private theorem jacobi_cyclic_zero (r : ℤ) (ab : ℤ × ℤ) :
    jacobiTerm r ab + jacobiTerm r (cycle r ab) +
      jacobiTerm r (cycle r (cycle r ab)) = 0 := by
  rcases ab with ⟨a,b⟩
  dsimp only [jacobiTerm, cycle, Equiv.coe_fn_mk]
  have hd : r-b-(r-a-b) = a := by omega
  have he : r-(r-a-b)-a = b := by omega
  rw [hd, he]
  rw [← ccc_cycle a b (r-a-b), ccc_cycle (r-a-b) a b]
  rw [← add_smul, ← add_smul]
  have hc : (1/4 : ℂ) * ((2*(a+b)-r : ℤ) : ℂ) * ((a-b : ℤ) : ℂ) +
      (1/4 : ℂ) * ((2*(b+(r-a-b))-r : ℤ) : ℂ) * ((b-(r-a-b) : ℤ) : ℂ) +
      (1/4 : ℂ) * ((2*((r-a-b)+a)-r : ℤ) : ℂ) * ((r-a-b-a : ℤ) : ℂ) = 0 := by
    push_cast
    ring
  rw [hc, zero_smul]

private theorem jacobi_sum_zero (r : ℤ) (v : Fock) :
    (∑ᶠ ab : ℤ × ℤ, jacobiTerm r ab v) = 0 := by
  let f : ℤ × ℤ → Fock := fun ab => jacobiTerm r ab v
  have hf : Function.HasFiniteSupport f := jacobiTerm_finite r v
  have hg : Function.HasFiniteSupport (fun ab => f (cycle r ab)) :=
    hf.fun_comp_of_injective (cycle r).injective
  have hh : Function.HasFiniteSupport (fun ab => f (cycle r (cycle r ab))) :=
    hf.fun_comp_of_injective ((cycle r).injective.comp (cycle r).injective)
  have hc₁ : (∑ᶠ ab, f (cycle r ab)) = ∑ᶠ ab, f ab := finsum_comp_equiv (cycle r)
  have hc₂ : (∑ᶠ ab, f (cycle r (cycle r ab))) = ∑ᶠ ab, f ab :=
    (finsum_comp_equiv (cycle r)).trans hc₁
  have hz : (∑ᶠ ab, f ab) + (∑ᶠ ab, f ab) + (∑ᶠ ab, f ab) = 0 := by
    calc
      _ = ((∑ᶠ ab, f ab) + (∑ᶠ ab, f (cycle r ab))) +
          (∑ᶠ ab, f (cycle r (cycle r ab))) := by rw [hc₁, hc₂]
      _ = ∑ᶠ ab, (f ab + f (cycle r ab) + f (cycle r (cycle r ab))) := by
        rw [← finsum_add_distrib hf hg]
        have hfg : Function.HasFiniteSupport (fun ab => f ab + f (cycle r ab)) := hf.add hg
        exact (finsum_add_distrib hfg hh).symm
      _ = 0 := by
        apply finsum_eq_zero_of_forall_eq_zero
        intro ab
        exact LinearMap.congr_fun (jacobi_cyclic_zero r ab) v
  have hthree : (3 : ℂ) • (∑ᶠ ab, f ab) = 0 := by
    simpa only [show (3 : ℂ) = 1+1+1 by norm_num, add_smul, one_smul] using hz
  exact (smul_eq_zero.mp hthree).resolve_left (by norm_num)

private theorem Qg_cc (p q : ℤ) :
    Qg*(c p*c q)-(c p*c q)*Qg = R p*c q-c p*R q := by
  calc
    _ = (Qg*c p+c p*Qg)*c q-c p*(Qg*c q+c q*Qg) := by noncomm_ring
    _ = _ := by rw [ward_c, ward_c]

private theorem jacobi_first (r p a : ℤ) (v : Fock) :
    ((1/2 : ℂ) * ((2*p-r : ℤ) : ℂ)) • rTerm p a (c (r-p) v) =
      jacobiTerm r (splitPair (p,a)) v := by
  dsimp only [rTerm, jacobiTerm, splitPair, Equiv.coe_fn_mk]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, smul_smul]
  rw [show r-a-(p-a) = r-p by omega, show 2*(a+(p-a))-r = 2*p-r by omega,
    show a-(p-a) = 2*a-p by omega]
  congr 1
  ring

private theorem jacobi_second (r p a : ℤ) (v : Fock) :
    -(((1/2 : ℂ) * ((2*p-r : ℤ) : ℂ)) • c p (rTerm (r-p) a v)) =
      jacobiTerm r (cycle r (p,a)) v := by
  dsimp only [rTerm, jacobiTerm, cycle, Equiv.coe_fn_mk]
  simp only [LinearMap.smul_apply, map_smul, smul_smul, Module.End.mul_apply]
  rw [show r-a-(r-p-a) = p by omega]
  have he := LinearMap.congr_fun (ccc_cycle p a (r-p-a)) v
  simp only [Module.End.mul_apply] at he
  rw [← he]
  simp only [← neg_smul]
  congr 1
  push_cast
  ring

/-- Actual finite triple-c expansion cancels by the Witt Jacobi polynomial. -/
theorem Qg_R (r : ℤ) : Qg*R r-R r*Qg = 0 := by
  apply LinearMap.ext
  intro v
  let f : ℤ × ℤ → Fock := fun ab => jacobiTerm r ab v
  let h₁ : ℤ × ℤ → Fock := fun pa => f (splitPair pa)
  let h₂ : ℤ × ℤ → Fock := fun pa => f (cycle r pa)
  have hf : Function.HasFiniteSupport f := jacobiTerm_finite r v
  have hh₁ : Function.HasFiniteSupport h₁ := hf.fun_comp_of_injective splitPair.injective
  have hh₂ : Function.HasFiniteSupport h₂ := hf.fun_comp_of_injective (cycle r).injective
  have hv := rTerm_finite r v
  have hw := rTerm_finite r (Qg v)
  have hmap := hv.fun_comp (map_zero Qg)
  change Qg (∑ᶠ p : ℤ, rTerm r p v) - (∑ᶠ p : ℤ, rTerm r p (Qg v)) = 0
  rw [map_finsum Qg hv, ← finsum_sub_distrib hmap hw]
  calc
    _ = ∑ᶠ p : ℤ, ∑ᶠ a : ℤ, (h₁ (p,a)+h₂ (p,a)) := by
      apply finsum_congr
      intro p
      have h := LinearMap.congr_fun (Qg_cc p (r-p)) v
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      simp only [rTerm, LinearMap.smul_apply, map_smul, Module.End.mul_apply]
      rw [← smul_sub, h, smul_sub]
      have hp₁ := rTerm_finite p (c (r-p) v)
      have hp₂ := rTerm_finite (r-p) v
      rw [show R p (c (r-p) v) = ∑ᶠ a : ℤ, rTerm p a (c (r-p) v) from rfl,
        show R (r-p) v = ∑ᶠ a : ℤ, rTerm (r-p) a v from rfl,
        map_finsum (c p) hp₂, smul_finsum' _ hp₁,
        smul_finsum' _ (hp₂.fun_comp (map_zero (c p)))]
      rw [← finsum_sub_distrib (hp₁.fun_comp (smul_zero _))
        ((hp₂.fun_comp (map_zero (c p))).fun_comp (smul_zero _))]
      apply finsum_congr
      intro a
      rw [sub_eq_add_neg, jacobi_first, jacobi_second]
    _ = ∑ᶠ pa : ℤ × ℤ, (h₁ pa+h₂ pa) := (finsum_curry _ (hh₁.add hh₂)).symm
    _ = (∑ᶠ pa : ℤ × ℤ, h₁ pa)+(∑ᶠ pa : ℤ × ℤ, h₂ pa) := finsum_add_distrib hh₁ hh₂
    _ = (∑ᶠ ab : ℤ × ℤ, f ab)+(∑ᶠ ab : ℤ × ℤ, f ab) := by
      change (∑ᶠ pa : ℤ × ℤ, f (splitPair pa)) +
        (∑ᶠ pa : ℤ × ℤ, f (cycle r pa)) = _
      rw [finsum_comp_equiv splitPair (f := f), finsum_comp_equiv (cycle r) (f := f)]
    _ = 0 := by rw [show (∑ᶠ ab, f ab) = 0 from jacobi_sum_zero r v]; simp

end D5.S3.Quantum.Fermionic.BcGhostBRST
