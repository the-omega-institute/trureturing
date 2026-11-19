/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRankThreeLocal
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalRankThreeLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original word solutions supply all premises of the local Dixon calculation. -/

import D5.S3.Arith.CharacterSums.PascadiRankThreeLocal
import D5.S3.Arith.CharacterSums.PascadiOriginalSingularPartners

/-! Nonzero Dixon triples in the actual derivative-zero family of the
original fixed-unit prime-cube word. -/

namespace D5.S3.Arith.CharacterSums.Original

open Polynomial

/-- Every actual triple in the chosen baseline’s derivative-zero family
uses the same common derivative and the original reduced slope. -/
theorem original_nonzero_dixon_rank_three {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (I J : ℝ) (hIJ : J ≤ I) (hJ : 1 ≤ J)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint) (e : Fin 3 → Endpoint)
    (hR : IsUnit (R.1 : ZMod (p^3))) (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hx : IsUnit ((physical R V base.1).1 : ZMod (p^3)))
    (hy : IsUnit ((physical R V base.2).1 : ZMod (p^3)))
    (hx₀ : IsUnit ((physical R V (e 0).1).1 : ZMod (p^3)))
    (hy₀ : IsUnit ((physical R V (e 0).2).1 : ZMod (p^3)))
    (hk : IsUnit (1 - a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))))
    (hbase : WordSolution (p^3) a₁ a₂ R V q base)
    (hword : ∀ i, WordSolution (p^3) a₁ a₂ R V q (e i))
    (hq : CoordinateBound I J q)
    (he : ∀ i, CoordinateBound I J (e i).1 ∧ CoordinateBound I J (e i).2)
    (hsize : 18 * (I*J) < (p : ℝ))
    (hgap : 10368 * (3 : ℝ)^9 * (I*J)^7 < (p : ℝ)^6)
    (hD : PrimeCube.residual (fun i => coeffL q (e i)) (fun i => coeffM q (e i))
      (fun i => coeffQ (e i)) (fun i => coeffR (e i)) (fun i => coeffS (e i)) ≠ 0)
    (hder : ∀ i, (pencil q base (e i)).derivative.eval₂ (Int.castRingHom (ZMod p))
      (ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
        ((V.1 : ZMod (p^3)) * (↑hR.unit⁻¹ : ZMod (p^3)))) = 0) :
    let : Fact p.Prime := ⟨hp⟩
    let β := (V.1 : ZMod (p^3)) * (↑hR.unit⁻¹ : ZMod (p^3))
    let b : ℤ := β.val
    let wordUnit : (ZMod (p^3))ˣ := ha₁.unit * ha₂.unit * ht.unit * hR.unit
    let lam : ℤ := (↑wordUnit⁻¹ : ZMod (p^3)).val
    let l := fun i => coeffL q (e i)
    let m := fun i => coeffM q (e i)
    let u := fun i => coeffQ (e i)
    let v := fun i => coeffR (e i)
    let w := fun i => coeffS (e i)
    let δbar : ZMod p := ((coeffR base + 2*b*coeffS base - lam*coeffM q base : ℤ) : ZMod p) /
      ((coeffL q base + b*coeffM q base : ℤ) : ZMod p)
    let δ : ℤ := δbar.val
    ((p : ℤ)^5 ∣ PrimeCube.residual l m u v w) ∧
      (¬ (p : ℤ)^6 ∣ PrimeCube.residual l m u v w) ∧
      ∃ g A B C d, PrimeCube.RankThreeKernel p l m u v w b lam δ I J g A B C d := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  dsimp only
  let β := (V.1 : ZMod (p^3)) * (↑hR.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let wordUnit : (ZMod (p^3))ˣ := ha₁.unit * ha₂.unit * ht.unit * hR.unit
  let α : ZMod (p^3) := ↑wordUnit⁻¹
  let lam : ℤ := α.val
  let l := fun i => coeffL q (e i)
  let m := fun i => coeffM q (e i)
  let u := fun i => coeffQ (e i)
  let v := fun i => coeffR (e i)
  let w := fun i => coeffS (e i)
  let M (f : Endpoint) := coeffM q f
  let L (f : Endpoint) := coeffL q f + b*M f
  let Q (f : Endpoint) := coeffQ f + b*coeffR f + b^2*coeffS f
  let D (f : Endpoint) := coeffR f + 2*b*coeffS f
  let δ₀ : ZMod p := ((D base - lam*M base : ℤ) : ZMod p) / (L base : ZMod p)
  let δ : ℤ := δ₀.val
  change ((p : ℤ)^5 ∣ PrimeCube.residual l m u v w) ∧
    (¬ (p : ℤ)^6 ∣ PrimeCube.residual l m u v w) ∧
    ∃ g A B C d, PrimeCube.RankThreeKernel p l m u v w b lam δ I J g A B C d
  let red := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = red β := by
    have hh := congrArg red (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  have hLu (f : Endpoint) (hf : WordSolution (p^3) a₁ a₂ R V q f)
      (hfx : IsUnit ((physical R V f.1).1 : ZMod (p^3)))
      (hfy : IsUnit ((physical R V f.2).1 : ZMod (p^3))) :
      IsUnit ((L f : ℤ) : ZMod p) := by
    have hobs := original_singular_unit_observations a₁ a₂ ha₁ ha₂ R V q
      f hR ht hf hfx hfy hk
    have H := hobs.1.map red
    rw [reduce_eval_at_lift red (endpointL q f) β b hb] at H
    simpa [L, M, endpointL, PrimeCube.linear, mul_comm] using H
  have hLu_base := hLu base hbase hx hy
  have hLu₀ := hLu (e 0) (hword 0) hx₀ hy₀
  have hval (f : Endpoint) (hf : WordSolution (p^3) a₁ a₂ R V q f) :
      (p : ℤ)^3 ∣ Q f - lam*L f := by
    have h := original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q f hR ht hf
    change -α * (endpointL q f).eval₂ (Int.castRingHom _) β +
      (endpointQ f).eval₂ (Int.castRingHom _) β = 0 at h
    have hb' : (b : ZMod (p^3)) = β := by simp [b]
    have hlam : (lam : ZMod (p^3)) = α := by simp [lam]
    have hL : (endpointL q f).eval b = L f := by
      simp [endpointL, PrimeCube.linear,L,M,mul_comm]
    have hQ : (endpointQ f).eval b = Q f := by
      simp [endpointQ, PrimeCube.quadratic,Q]
      ring
    have heval (F : ℤ[X]) :
        F.eval₂ (Int.castRingHom (ZMod (p^3))) (b : ZMod (p^3)) =
          (↑(F.eval b : ℤ) : ZMod (p^3)) := eval₂_at_apply (Int.castRingHom (ZMod (p^3))) b
    rw [← hb', heval, heval, hL, hQ] at h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hlam]
    linear_combination h
  have hvalp (f : Endpoint) (hf : WordSolution (p^3) a₁ a₂ R V q f) :
      (Q f : ZMod p) = (lam : ZMod p) * (L f : ZMod p) := by
    have hd : (p : ℤ) ∣ Q f - lam * L f := by
      simpa only [pow_one] using ((pow_dvd_pow (p : ℤ) (by decide : 1 ≤ 3)).trans (hval f hf))
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    push_cast at hz
    exact sub_eq_zero.mp hz
  have hδ : (δ : ZMod p) * (L base : ZMod p) =
      (D base : ZMod p) - (lam : ZMod p) * (M base : ZMod p) := by
    have hcast : (δ : ZMod p) = δ₀ := by simp [δ]
    rw [hcast]
    dsimp [δ₀]
    push_cast
    exact div_mul_cancel₀ _ hLu_base.ne_zero
  have hder_exp (f g : Endpoint) : (pencil q f g).derivative.eval b =
      L f * D g + M f * Q g - L g * D f - M g * Q f := by
    simp [pencil, endpointL, endpointQ, PrimeCube.linear, PrimeCube.quadratic, L, M, Q, D,
      derivative_add, derivative_sub, derivative_mul, derivative_pow]
    ring
  have hder_z (i : Fin 3) :
      (((pencil q base (e i)).derivative.eval b : ℤ) : ZMod p) = 0 := by
    change (Int.castRingHom (ZMod p)) ((pencil q base (e i)).derivative.eval b) = 0
    rw [← Polynomial.eval₂_at_apply]
    simp only [Int.coe_castRingHom, hb]
    exact hder i
  have hder_mod (i : Fin 3) : (D (e i) : ZMod p) =
      (δ : ZMod p)*(L (e i) : ZMod p) + (lam : ZMod p)*(M (e i) : ZMod p) := by
    have H := hder_z i
    rw [hder_exp] at H
    push_cast at H
    rw [hvalp (e i) (hword i), hvalp base hbase] at H
    apply hLu_base.mul_left_cancel
    linear_combination H - (L (e i) : ZMod p) * hδ
  have hder' (i : Fin 3) : (p : ℤ) ∣ D (e i) - δ*L (e i) - lam*M (e i) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    linear_combination hder_mod i
  have hpair (i : Fin 3) : PrimeCube.pair l m u v w i = pencil q (e 0) (e i) := rfl
  have hpairval (i : Fin 3) : (p : ℤ)^3 ∣ (PrimeCube.pair l m u v w i).eval b := by
    rw [hpair]
    exact original_pencil_dvd hp a₁ a₂ ha₁ ha₂ R V q (e 0) (e i)
      hR ht (hword 0) (hword i)
  have hpairder (i : Fin 3) : (p : ℤ) ∣ (PrimeCube.pair l m u v w i).derivative.eval b := by
    rw [hpair, hder_exp]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hvalp (e i) (hword i), hder_mod i, hvalp (e 0) (hword 0), hder_mod 0]
    ring
  have hcoeff (i : Fin 3) := actual_coefficient_bounds I J q (e i) hq (he i).1 (he i).2
  have hI := hJ.trans hIJ
  have hIJ₀ : 0 ≤ I * J := by positivity
  have hbound := PrimeCube.actual_residual_height l m u v w I J 3 hI hJ (by norm_num)
    (fun i => (hcoeff i).1) (fun i => (hcoeff i).2.1)
    (fun i => (hcoeff i).2.2.1.trans (by nlinarith [sq_nonneg I]))
    (fun i => (hcoeff i).2.2.2.1.trans (by nlinarith [hIJ₀]))
    (fun i => (hcoeff i).2.2.2.2.trans (by nlinarith [sq_nonneg J]))
  have hD6 : ¬ (p : ℤ)^6 ∣ PrimeCube.residual l m u v w := by
    intro h
    have H : (p : ℝ)^6 ≤ |((PrimeCube.residual l m u v w : ℤ) : ℝ)| := by
      exact_mod_cast Int.le_abs_of_dvd hD h
    exact (not_lt_of_ge H) (hbound.trans_lt hgap)
  refine ⟨PrimeCube.actual_residual_dvd_fifth l m u v w p b hLu₀ (hpairval 1)
    (hpairval 2) (hpairder 1) (hpairder 2), hD6, ?_⟩
  exact PrimeCube.nonzero_dixon_rank_three l m u v w b lam δ I J hI hJ hodd
    (fun i => (hcoeff i).1) (fun i => (hcoeff i).2.1) (fun i => (hcoeff i).2.2.1)
    (fun i => (hcoeff i).2.2.2.1) (fun i => (hcoeff i).2.2.2.2)
    hsize (fun i => hval (e i) (hword i)) hder' hD6

end D5.S3.Arith.CharacterSums.Original
