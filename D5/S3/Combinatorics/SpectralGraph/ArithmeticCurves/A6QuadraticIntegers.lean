/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticIntegers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticIntegers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A6QuadraticIntegers at the full original arithmetic domain -/

import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6EllipticModels
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Exact full integral closure for the received quadratic field.
Source: supplied S.coset, PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02,
blob8f84b430e880aeef5747688e95608220bbfc96a2. Original Nikandish
problem and Ma/Nikandish/Zhang attribution remain. -/
set_option autoImplicit false
noncomputable section
open scoped Classical QuadraticAlgebra
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuadraticIntegers
open A6EllipticModels
open Polynomial

def theta : K:=(1+sqrtD)/2

theorem theta_integral : IsIntegral ℤ theta := by
  let p : ℤ[X]:=X^2+(-X-C 10911)
  have hp : p.Monic := by
    apply monic_X_pow_add
    have hX : degree (-X:ℤ[X])<(2:WithBot ℕ):=by simp
    have hC : degree (C (10911:ℤ))<(2:WithBot ℕ):=
      lt_of_le_of_lt degree_C_le (by norm_num)
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt_iff.mpr ⟨hX,hC⟩)
  refine ⟨p,hp,?_⟩
  simp only [p,map_add,map_pow,map_sub,map_neg,aeval_X,aeval_C]
  ext <;> norm_num [theta,sqrtD,QuadraticAlgebra.omega,
    QuadraticAlgebra.div_def,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def,
    pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

private theorem scaled_square_integer (v : ℚ) (N : ℤ)
    (h : 43645*v^2=(N:ℚ)) : ∃ s : ℤ,(s:ℚ)=v := by
  have hd : (v.den:ℚ)≠0:=by exact_mod_cast v.den_ne_zero
  have he : (43645:ℤ)*v.num^2=N*(v.den:ℤ)^2 := by
    have h':=h
    rw [←Rat.num_div_den v] at h'
    field_simp [hd] at h'
    simpa only [mul_comm] using (show (43645:ℤ)*v.num^2=(v.den:ℤ)^2*N by exact_mod_cast h')
  have hdvd : (v.den:ℤ)^2∣(43645:ℤ)*v.num^2:=⟨N,by linarith [he]⟩
  have hc : IsCoprime ((v.den:ℤ)^2) (v.num^2):=(Rat.isCoprime_num_den v).symm.pow
  have hD : (v.den:ℤ)^2∣(43645:ℤ):=hc.dvd_of_dvd_mul_right hdvd
  have hsf : Squarefree (43645:ℤ):=by
    apply Int.squarefree_natCast.mpr
    have h5 : Squarefree (5:ℕ):=(by norm_num : Nat.Prime 5).squarefree
    have h7 : Squarefree (7:ℕ):=(by norm_num : Nat.Prime 7).squarefree
    have h29 : Squarefree (29:ℕ):=(by norm_num : Nat.Prime 29).squarefree
    have h43 : Squarefree (43:ℕ):=(by norm_num : Nat.Prime 43).squarefree
    have h57 : Squarefree (5*7:ℕ):=
      (Nat.squarefree_mul (by decide : Nat.Coprime 5 7)).2 ⟨h5,h7⟩
    have h5729 : Squarefree (5*7*29:ℕ):=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5*7) 29)).2 ⟨h57,h29⟩
    exact (Nat.squarefree_mul (by decide : Nat.Coprime (5*7*29) 43)).2 ⟨h5729,h43⟩
  have hu : IsUnit (v.den:ℤ):=hsf _ (by simpa only [pow_two] using hD)
  have hden : v.den=1:=by
    rw [Int.isUnit_iff] at hu
    rcases hu with hu|hu <;> have hp:=v.den_pos <;> omega
  exact ⟨v.num,(Rat.den_eq_one_iff v).mp hden⟩

private theorem trace_norm_integers (x : K) (hx : IsIntegral ℤ x) :
    ∃ t n : ℤ,(t:ℚ)=2*x.re ∧ (n:ℚ)=x.re^2-43645*x.im^2 := by
  have hs : IsIntegral ℤ (star x):=map_isIntegral_int (starRingAut:RingAut K) hx
  have htrace : algebraMap ℚ K (2*x.re)=x+star x:=by
    ext <;> simp [QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> ring
  have hnorm : algebraMap ℚ K (x.re^2-43645*x.im^2)=x*star x:=by
    ext <;> simp [pow_two,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> ring
  have hti : IsIntegral ℤ (2*x.re) :=
    isIntegral_algebraMap_iff.mp (htrace.symm ▸ hx.add hs)
  have hni : IsIntegral ℤ (x.re^2-43645*x.im^2) :=
    isIntegral_algebraMap_iff.mp (hnorm.symm ▸ hx.mul hs)
  obtain ⟨t,ht⟩:=IsIntegrallyClosed.isIntegral_iff.mp hti
  obtain ⟨n,hn⟩:=IsIntegrallyClosed.isIntegral_iff.mp hni
  exact ⟨t,n,ht,hn⟩

private theorem parity_of_norm (t s n : ℤ) (h : t^2-43645*s^2=4*n) :
    (2:ℤ)∣t-s := by
  have hm:=congrArg (fun z : ℤ=>z%4) h
  have ht : 0≤t%4 ∧ t%4<4:=⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  have hs : 0≤s%4 ∧ s%4<4:=⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  rcases ht with ⟨htlo,hthi⟩
  rcases hs with ⟨hslo,hshi⟩
  interval_cases htm : t%4 <;> interval_cases hsm : s%4 <;>
    norm_num [pow_two,Int.sub_emod,Int.mul_emod,htm,hsm] at hm <;> omega

/-- No half-integer fiber is excluded: this is a characterization of
every element of the entire integral closure. -/
theorem integral_iff_integer_coordinates (x : K) :
    IsIntegral ℤ x ↔ ∃ m n : ℤ,x=(m:K)+(n:K)*theta := by
  constructor
  · intro hx
    obtain ⟨t,n,ht,hn⟩:=trace_norm_integers x hx
    have hv : 43645*(2*x.im)^2=((t^2-4*n:ℤ):ℚ) := by
      push_cast
      rw [ht,hn]
      ring
    obtain ⟨s,hs⟩:=scaled_square_integer (2*x.im) (t^2-4*n) hv
    have he : t^2-43645*s^2=4*n := by
      have heQ : (t:ℚ)^2-43645*(s:ℚ)^2=4*(n:ℚ) := by rw [ht,hs,hn];ring
      exact_mod_cast heQ
    obtain ⟨m,hm⟩:=parity_of_norm t s n he
    refine ⟨m,s,?_⟩
    have hmQ : (t:ℚ)-(s:ℚ)=2*(m:ℚ):=by exact_mod_cast hm
    ext <;>
      simp [theta,sqrtD,QuadraticAlgebra.omega,
        QuadraticAlgebra.div_def,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def,
        QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    all_goals linarith [ht,hs,hmQ]
  · rintro ⟨m,n,rfl⟩
    exact isIntegral_intCast m |>.add ((isIntegral_intCast n).mul theta_integral)

/-- The exact received full ring O_K=Z[(1+sqrt43645)/2], as an equality
of actual subalgebras of the field, rather than a chosen order. -/
theorem full_ring_eq_adjoin : integralClosure ℤ K=Algebra.adjoin ℤ {theta} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨m,n,rfl⟩:=(integral_iff_integer_coordinates x).mp hx
    exact add_mem ((Algebra.adjoin ℤ {theta}).algebraMap_mem m)
      (mul_mem ((Algebra.adjoin ℤ {theta}).algebraMap_mem n)
        (Algebra.subset_adjoin (by simp)))
  · apply Algebra.adjoin_le
    intro x hx
    have he : x=theta:=Set.mem_singleton_iff.mp hx
    rw [he]
    exact theta_integral

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuadraticIntegers
