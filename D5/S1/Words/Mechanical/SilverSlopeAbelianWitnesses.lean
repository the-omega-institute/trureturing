/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The two explicit silver witness families have their claimed minimum periods. -/
/-
Judgement form:
  silver_w2_min_period:
    proof_shape: content
    escape_witness: silver_w2_period k hk: AbelianPeriod (lowerMechanicalFactor silverSlope 0
      (2*P (k + 1)*(P (k + 1)+P k)+P (k + 1)-1) (2*P (k + 1)+P k)) (2*P (k + 1))
    Non-binding step: This live existence theorem and the live exclusions remain substantive
      after inlining. Nat.find_eq_iff supplies only the final minimum packaging.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
  silver_wr_min_period:
    proof_shape: content
    escape_witness: silver_wr_period k hk: AbelianPeriod of the factor of length (2*P (k + 1)+1)*(P (k + 1)+P k)-(if k%2=1 then 1 else 2), at (if k%2=1 then 0 else P (k + 1)+1), with period P (k + 1)+P k
    Non-binding step: This live period construction and all-smaller-period exclusions remain
      substantive after inlining. There is no pinned minimum-period bypass.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
admission_basis: escape-witness
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import D5.S1.Words.Mechanical.SilverSlopeAbelianWitnessPeriods
import D5.S1.Words.Mechanical.SilverSlopeAbelianWitnessExclusions
namespace D5.S1.Words.Mechanical
open D5.S1.Recurrence.PellCompanionGcd

theorem silver_w2_min_period (k : Nat) (hk : 1 ≤ k) :
    0 < 2 * P (k + 1) * (P (k + 1) + P k) + P (k + 1) - 1 ∧
    minAbelianPeriod (lowerMechanicalFactor silverSlope 0
      (2 * P (k + 1) * (P (k + 1) + P k) + P (k + 1) - 1)
      (2 * P (k + 1) + P k)) = 2 * P (k + 1) := by
  classical
  let n := 2*P (k + 1)*(P (k + 1)+P k)+P (k + 1)-1
  let i := 2*P (k + 1)+P k
  have hq := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have ht : 0<P k := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    exact (by have hs := (pell_companion_step j).1; obtain ⟨j, hj⟩ := companion_odd j; omega : 0 < P (j + 1))
  have hn : 0<n := by
    have hmul := Nat.mul_pos (show 0<2*P (k + 1) by omega)
      (show 0<P (k + 1)+P k by omega)
    dsimp [n]
    omega
  have hp := silver_w2_period k hk
  change AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) (2*P (k + 1)) at hp
  have hex : ∃ m, AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) m := ⟨_,hp⟩
  refine ⟨hn,?_⟩
  change minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i)=2*P (k + 1)
  rw [minAbelianPeriod]
  split
  · rename_i h
    apply (Nat.find_eq_iff h).2
    refine ⟨hp,?_⟩
    intro m hmlt hmp
    have hm0 : 0<m := hmp.1
    by_cases hmq : m=P (k + 1)
    · subst m
      exact silver_no_q_period k n i hk le_rfl (fun _ => Or.inl rfl) hmp
    · by_cases hmr : m=P (k + 1)+P k
      · subst m
        exact silver_w2_no_r_period k hk hmp
      · exact silver_short_period_exclusion k n i m hk le_rfl hm0 hmlt hmq hmr hmp
  · rename_i h
    exact False.elim (h hex)
#print axioms silver_w2_min_period

theorem silver_wr_min_period (k : Nat) (hk : 1 ≤ k) :
    0 < (2 * P (k + 1) + 1) * (P (k + 1) + P k) -
      (if k % 2 = 1 then 1 else 2) ∧
    minAbelianPeriod (lowerMechanicalFactor silverSlope 0
      ((2 * P (k + 1) + 1) * (P (k + 1) + P k) -
        (if k % 2 = 1 then 1 else 2))
      (if k % 2 = 1 then 0 else P (k + 1) + 1)) = P (k + 1) + P k := by
  classical
  let q := P (k + 1)
  let t := P k
  let r := q+t
  let n := (2*q+1)*r-(if k%2=1 then 1 else 2)
  let i := if k%2=1 then 0 else q+1
  have hq : 0<q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have ht : 0<t := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    exact (by have hs := (pell_companion_step j).1; obtain ⟨j, hj⟩ := companion_odd j; omega : 0 < P (j + 1))
  have htq : t<q := (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : P k < P (k + 1))
  have hnlow : 2*q*r+q-1≤n := by
    have hmul := Nat.mul_pos (show 0<2*q by omega) (show 0<r by dsimp [r];omega)
    have hs1 := Nat.sub_add_cancel (show 1≤2*q*r+q by omega)
    have hs2 : 2≤(2*q+1)*r := by dsimp [r];nlinarith
    dsimp [n]
    split <;>
      nlinarith [Nat.sub_add_cancel (show 1≤(2*q+1)*r by omega),
        Nat.sub_add_cancel hs2,show r=q+t from rfl]
  have hn : 0<n := by
    have hmul := Nat.mul_pos (show 0<2*q by omega) (show 0<r by dsimp [r];omega)
    omega
  have hp := silver_wr_period k hk
  change AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) r at hp
  have hex : ∃ m, AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) m := ⟨_,hp⟩
  refine ⟨hn,?_⟩
  change minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i)=r
  rw [minAbelianPeriod]
  split
  · rename_i h
    apply (Nat.find_eq_iff h).2
    refine ⟨hp,?_⟩
    intro m hmlt hmp
    have hm0 : 0<m := hmp.1
    by_cases hmq : m=q
    · subst m
      apply silver_no_q_period k n i hk hnlow _ hmp
      intro heven
      right
      dsimp [i]
      have he0 := Nat.even_iff.mp heven
      rw [if_neg (by omega)]
    · have hmr : m≠P (k + 1)+P k := by change m≠r;omega
      have hm2 : m<2*P (k + 1) := by change m<2*q;dsimp [r] at hmlt;omega
      exact silver_short_period_exclusion k n i m hk hnlow hm0 hm2 hmq hmr hmp
  · rename_i h
    exact False.elim (h hex)
#print axioms silver_wr_min_period
end D5.S1.Words.Mechanical
