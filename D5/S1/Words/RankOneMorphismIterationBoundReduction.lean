/- GID: D5/S1/Words/RankOneMorphismIterationBoundReduction
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundReduction
   mirror-E: none(waiver:one-sided-source-period-reduction)
   anchors: []
   digest: Arbitrary one-sided UAP periods yield actual original cyclic witnesses. -/
import D5.S1.Words.RankOneMorphismIterationBoundSourceResidues
import D5.S1.Words.RankOneMorphismIterationBoundExtraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

theorem indexed_digit_coding (hp : Prolongable f) (v : List (Fin p.lam)) (i : ℕ) :
    p.height p.fixedWord (p.lam^v.length*i+p.digitValue v) =
      p.coding (p.heightMachine.toDFA.evalFrom (p.indexedFixedWord i) v) := by
  rw [← p.indexedFixedWord_coding hp,
    p.indexedFixedWord_copy hp i v.length (p.digitValue v) (p.digitValue_lt v),
    p.uniform_iter_eval]

/-- Coprime residue cosets transfer the actual ray to d lambda^t while
    retaining its given one-sided phase. -/
theorem reduce_coprime_ray (hp : Prolongable f) (q t r : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q)
    (h : ∀ j, p.height p.fixedWord (r+j*(q*p.lam^t)) = p.height p.fixedWord r) :
    ∀ j, p.height p.fixedWord (r+j*(p.d*p.lam^t)) = p.height p.fixedWord r := by
  let L := p.lam^t
  have hL : 0 < L := pow_pos (by have := p.lam_ge_two; omega) _
  let e := r/L
  let u := r%L
  have hu : u < p.lam^t := Nat.mod_lt _ hL
  obtain ⟨v,hv,hval⟩ := p.digits_exist t u hu
  have hr : L*e+u = r := by exact Nat.div_add_mod _ _
  have hcode (j : ℕ) : p.coding (p.heightMachine.toDFA.evalFrom (p.indexedFixedWord (e+j*q)) v) =
      p.height p.fixedWord r := by
    rw [← p.indexed_digit_coding hp v, hv,hval]
    convert h j using 1 <;> congr 1 <;> dsimp [L] at hr ⊢ <;> nlinarith
  intro j
  let γ := p.indexedFixedWord (e+j*p.d)
  have hγ : ((e+j*p.d : ℕ) : ZMod q) ∈ p.occurrenceResidues q γ := ⟨_,rfl,rfl⟩
  have heγ : (e : ZMod q) ∈ p.occurrenceResidues q γ := by
    apply (p.occurrence_coset hp p.allStatesReturn q hq hcop γ hγ (e : ZMod q)).mpr
    have hd := (p.returnSubgroup hp q hq hcop).nsmul_mem (p.d_mem_return hp q hq hcop) j
    have hh := (p.returnSubgroup hp q hq hcop).neg_mem hd
    simpa only [Nat.cast_add,Nat.cast_mul,nsmul_eq_mul,sub_add_eq_sub_sub,sub_self,zero_sub] using hh
  obtain ⟨i,hie,hig,hres⟩ := p.occurrence_tail hp q hq hcop γ heγ e
  have hmod : i%q = e%q := by
    exact (ZMod.natCast_eq_natCast_iff i e q).mp hres
  have hdiv : q ∣ i-e := by
    apply (Nat.modEq_iff_dvd' hie).mp
    exact hmod.symm
  obtain ⟨k,hk⟩ := hdiv
  have hik : i = e+k*q := by nlinarith [Nat.sub_add_cancel hie]
  have hh := hcode k
  rw [← hik,hig] at hh
  rw [← p.indexed_digit_coding hp v (e+j*p.d),hv,hval] at hh
  convert hh using 1 <;> congr 1 <;> dsimp [L] at hr ⊢ <;> nlinarith

/-- Full necessity: arbitrary preperiod and arbitrary period yield an actual
    original four-word witness. The paper's period theorem is not assumed. -/
theorem original_of_uap (hp : Prolongable f) (huap : UltimatelyAbelianPeriodic p.fixedWord) :
    ∃ K : ℕ, 1 ≤ K ∧ OriginalCyclicBlockWitness f K := by
  obtain ⟨r,P,hP,h⟩ := p.height_ray_of_uap (p.fixedWord_height_finite hp) huap
  obtain ⟨q,t,hq,hcop,hdiv⟩ := p.strip_period P hP
  have hsub := p.height_subray hdiv h
  have hnorm := p.reduce_coprime_ray hp q t r hq hcop.symm hsub
  let T := t+(r+1)
  have hbig : r < p.d*p.lam^T := by
    have hh := (Nat.lt_two_pow_self : r < 2^r).trans_le (Nat.pow_le_pow_left p.lam_ge_two r)
    have ht : r ≤ T := by dsimp [T]; omega
    have hpow := Nat.pow_le_pow_right (by have := p.lam_ge_two; omega : 0 < p.lam) ht
    have hd : 1 ≤ p.d := p.d_pos
    have hm := Nat.mul_le_mul_right (p.lam^T) hd
    simp only [one_mul] at hm
    omega
  have hdiv' : p.d*p.lam^t ∣ p.d*p.lam^T := by
    dsimp [T]
    rw [pow_add,← Nat.mul_assoc]
    exact dvd_mul_right _ _
  have hnorm' := p.height_subray hdiv' hnorm
  exact ⟨T+1,by omega,(p.original_iff_samples T).mpr (p.samples_of_fixedWord_ray hp T r hbig hnorm')⟩

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
