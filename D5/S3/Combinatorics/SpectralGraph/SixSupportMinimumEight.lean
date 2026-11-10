/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportMinimumEight
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportMinimumEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete minimum-eight dependency reduction through 108 unbounded exponent brackets. -/
import D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointGeometry
import D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoTail
import D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedCompletion

/-! Source S.minimum8 and every row of S.min8csv at PR9. The full 108-row
certificate concerns a fixed middle exponent and every unbounded c>b.
This route does not import the 8658 endpoint-two base. The cumulative
minimum-through-eight result still inherits the earlier 27562 and smaller
bases. Original source Sturm/Bareiss reports remain attributed reports;
current kernel signs below evaluate the literal cubic, whose identity with
the actual six-cell characteristic quotient is proved. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportMinimumEight
open SixSupportClassificationAlgebra
open SixSupportEndpointGeometry
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

private def lowerTable : List ℕ := [140, 148, 156, 162, 167, 171, 175, 178, 181, 183, 185, 186, 188, 189, 190, 190, 191, 191, 191, 191, 191, 191, 191, 191, 191, 190, 190, 190, 189, 189, 188, 188, 187, 186, 186, 185, 184, 184, 183, 182, 181, 181, 180, 179, 178, 178, 177, 176, 175, 174, 173, 172, 172, 171, 170, 169, 168, 167, 166, 165, 164, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119]
private def lower (i : Fin 108) : ℕ := lowerTable[i.val]'(by simpa [lowerTable] using i.isLt)
private def Q (b c : ℤ) : ℤ :=
  (b^2+63)*c^3+(b^3-241*b^2+133*b+427)*c^2+
    7*(b-1)*(19*b+21)*c+7*(b-1)*(b+7)*(9*b+7)

private theorem finite_signs : ∀ i : Fin 108,
    11+i.val<lower i ∧ Q ((11+i.val : ℕ) : ℤ) (lower i)<0 ∧
      0<Q ((11+i.val : ℕ) : ℤ) (lower i+1) := by
  decide +kernel

private theorem cubic_identity (b c : ℤ) :
    (Q b c : ℝ)=h (8 : ℝ) b c 1 := by
  rw [SixSupportEndpointSmallGaps.endpoint_identity]
  push_cast
  dsimp [Q,SixSupportEndpointSmallGaps.cubic]
  push_cast
  ring

/-- Every one of the complete 108 fixed-middle source rows excludes all
integer c above that middle exponent, with no upper bound on c. -/
theorem fixed_middle_nonzero (b c : ℕ) (hb : 11≤b) (hb' : b≤118) (hbc : b<c) :
    h (8 : ℝ) b c 1≠0 := by
  let i : Fin 108:=⟨b-11,by omega⟩
  have hi : 11+i.val=b:=by dsimp [i];omega
  obtain ⟨hbL,hL,hU⟩:=finite_signs i
  rw [hi] at hbL hL hU
  have hLR : h (8 : ℝ) b (lower i) 1<0:=by
    have hh : (Q b (lower i) : ℝ)<0:=by exact_mod_cast hL
    simpa only [cubic_identity,Int.cast_natCast] using hh
  have hUR : 0<h (8 : ℝ) b ((lower i : ℝ)+1) 1:=by
    have hh : 0<(Q b (lower i+1) : ℝ):=by exact_mod_cast hU
    simpa only [cubic_identity,Int.cast_add,Int.cast_natCast,Int.cast_one] using hh
  obtain ⟨r,hr,hr0⟩:=intermediate_value_Icc (show (lower i : ℝ)≤lower i+1 by linarith)
    (show ContinuousOn (fun x : ℝ=>h (8 : ℝ) b x 1) (Set.Icc (lower i) (lower i+1)) by simp_rw [SixSupportEndpointSmallGaps.endpoint_identity];unfold SixSupportEndpointSmallGaps.cubic;fun_prop)
    (show (0 : ℝ)∈Set.Icc (h (8 : ℝ) b (lower i) 1) (h (8 : ℝ) b (lower i+1) 1) from ⟨hLR.le,hUR.le⟩)
  have hrl : (lower i : ℝ)<r:=by
    by_contra hn
    have he : r=lower i:=le_antisymm (le_of_not_gt hn) hr.1
    rw [he] at hr0
    linarith
  have hru : r<(lower i : ℝ)+1:=by
    by_contra hn
    have he : r=(lower i : ℝ)+1:=le_antisymm hr.2 (le_of_not_gt hn)
    rw [he] at hr0
    linarith
  intro hc
  have hbr : (b : ℝ)<r:=lt_trans (by exact_mod_cast hbL) hrl
  have hu:=((geometry_one 8 b (by norm_num) (by exact_mod_cast (show 8≤b by omega))).2
    c (by exact_mod_cast hbc) hc).2 r hbr hr0
  have hcl : (lower i : ℝ)<c:=by simpa [hu] using hrl
  have hcu : (c : ℝ)<(lower i : ℝ)+1:=by simpa [hu] using hru
  have : lower i<c:=by exact_mod_cast hcl
  have : c<lower i+1:=by exact_mod_cast hcu
  omega

/-- The full endpoint-one exclusion for every fully distinct integer triple
of minimum eight, using the two written small-gap cases and all 108 rows. -/
theorem endpoint_one_nonzero (b c : ℕ) (hb : 8<b) (hbc : b<c) : h (8 : ℝ) b c 1≠0 := by
  by_cases h9 : b=9
  · subst b
    exact SixSupportEndpointSmallGaps.integer_nonzero 8 c (by norm_num) (0 : Fin 2)
      (by simpa using hbc)
  by_cases h10 : b=10
  · subst b
    exact SixSupportEndpointSmallGaps.integer_nonzero 8 c (by norm_num) (1 : Fin 2)
      (by simpa using hbc)
  by_cases hb118 : b≤118
  · exact fixed_middle_nonzero b c (by omega) hb118 hbc
  · intro hc
    obtain ⟨gamma,hgl,hgu,hg,hpos,hzero⟩:=threshold_one 8 (by norm_num)
    have hp:=(geometry_one 8 b (by norm_num) (by exact_mod_cast hb.le)).1.mp ⟨c,by exact_mod_cast hbc,hc⟩
    have hbg:=(hpos b (by exact_mod_cast hb.le)).mp hp
    norm_num at hgu
    have hble : (119 : ℝ)≤b:=by exact_mod_cast (show 119≤b by omega)
    linarith

/-- Complete actual-ideal-graph minimum-eight nonintegrality on the fully
distinct domain. The written endpoint-two rectangle suffices at c>=10. -/
theorem distinct_actual (p : Fin 3 → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 8<b) (hbc : b<c) :
    ¬ActualLaplacianIntegral (modulus p (exponents 8 b c)) := by
  intro hi
  rcases endpoint_one_or_two p hp hinj 8 b c (by norm_num) hb.le hbc.le hi with h1|h2
  · exact endpoint_one_nonzero b c hb hbc h1
  · obtain ⟨_,hc⟩:=SixSupportEndpointTwoTail.rectangle 8 b c (by norm_num)
      (by exact_mod_cast hb.le) (by exact_mod_cast hbc.le) h2
    have hc10 : (10 : ℝ)≤c:=by exact_mod_cast (show 10≤c by omega)
    norm_num at hc
    linarith

/-- Every ordered positive integer triple with minimum exactly eight,
including both kinds of repetition, at arbitrary distinct primes. -/
theorem result (p : Fin 3 → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 8≤b) (hbc : b≤c) :
    ¬ActualLaplacianIntegral (modulus p (exponents 8 b c)) := by
  by_cases h8 : b=8
  · subst b
    exact SixSupportRepeatedCompletion.result p hp hinj 8 c (by norm_num) (by omega)
  by_cases he : b=c
  · subst c
    let e : Equiv.Perm (Fin 3):=Equiv.swap 0 2
    have hk : exponents 8 b b ∘ e=exponents b b 8:=by funext i;fin_cases i <;>rfl
    have hm : modulus (p ∘ e) (exponents 8 b b ∘ e)=modulus p (exponents 8 b b):=
      Equiv.prod_comp e (fun i=>p i^exponents 8 b b i)
    rw [hk] at hm
    rw [←hm]
    exact SixSupportRepeatedCompletion.result (p ∘ e) (fun i=>hp (e i))
      (hinj.comp e.injective) b 8 (by omega) (by norm_num)
  exact distinct_actual p hp hinj b c (by omega) (by omega)
end D5.S3.Combinatorics.SpectralGraph.SixSupportMinimumEight
