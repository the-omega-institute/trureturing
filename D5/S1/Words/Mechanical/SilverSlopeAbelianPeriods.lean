/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Peltomäki's silver-slope abelian-period conjecture. -/
/-
Judgement form:
  claim:
    proof_shape: definition
    escape_witness: none (literal definition)
  result:
    proof_shape: content
    escape_witness: silver_w2_min_period k hk: 0<N₂(k) ∧ minAbelianPeriod (lowerMechanicalFactor
      silverSlope 0 N₂(k) I₂(k))=2*P (k + 1), where N₂(k)=2*P (k + 1)*(P (k + 1)+P k)+P (k + 1)-1 and I₂(k)=2*P (k + 1)+P k; silver_wr_min_period gives the
      adjacent-sum family
    Non-binding step: Both exact-minimum witness families are live in the reverse inclusion.
      Inlining their constructions gives genuine content; the main conclusion cannot be obtained
      from any located pinned-Mathlib/frozen-D5 period theorem.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d);
      D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
      (sha256:31fb069a0187ae500aa0a39e052a8deaceee7eb0f963bcc75879f9f575b26ff1);
      D5/S1/Words/Mechanical/MechanicalBalance
      (sha256:db7434e78bc669a2f0d5711175f8f744fc6dfba359dd5414cc8c05c753ad3399);
      D5/S1/Words/Mechanical/MechanicalFactorComplexity
      (sha256:9b83310d03f384fa38264d66462adfe64f238b0be826575d08630dad3141f15a)
admission_basis: open-problem-resolution (#13073; Proved)
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import D5.S1.Words.Mechanical.SilverSlopeAbelianPeriodTerrain
import D5.S1.Words.Mechanical.SilverSlopeAbelianWitnesses
import D5.S1.Words.Mechanical.SilverSlopeAbelianUpperInclusion
namespace D5.S1.Words.Mechanical
open D5.S1.Recurrence.PellCompanionGcd
open D5.S1.Words.Complexity
/--
J. Peltomäki, "Abelian periods of factors of Sturmian words", J. Number Theory
214 (2020), Conjecture (p. 283, line 1722): "Let $\alpha = [0; \overline{2}]$.
The abelian period set of a Sturmian word of slope $\alpha$ is $\mathcal{Q}^+_\alpha
\cup \mathcal{M}_\alpha$."
-/
def claim : Prop := silverAbelianPeriodSet = silverCandidateSet

set_option maxHeartbeats 2000000 in
theorem result : claim := by
  classical
  have hlength : ∀ w : List Bool, 0<w.length → AbelianPeriod w w.length := by
    intro w hw
    have hempty : (parikh []) < (parikh w) := by
      simp only [lt_iff_le_and_ne, Prod.le_def, and_assoc]
      refine ⟨Nat.zero_le _,Nat.zero_le _,?_⟩
      intro hz
      have hh := congrArg (fun p : Nat×Nat => p.1+p.2) hz
      have hs := List.count_false_add_count_true w
      simp only [parikh,List.count_nil] at hh
      omega
    refine ⟨hw,[],[],[w],by simp,by simp,by simp,by simp,?_⟩
    exact ⟨parikh w,by simp,hempty,hempty⟩
  have hmin : ∀ n i : Nat, 0<n →
      AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i)
        (minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i)) ∧
      ∀ m<minAbelianPeriod (lowerMechanicalFactor silverSlope 0 n i),
        ¬ AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) m := by
    intro n i hn
    have hw : 0<(lowerMechanicalFactor silverSlope 0 n i).length := by
      simpa [lowerMechanicalFactor] using hn
    have hex : ∃ m, AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) m :=
      ⟨_,hlength _ hw⟩
    rw [minAbelianPeriod]
    split
    · rename_i h
      exact ⟨Nat.find_spec h,fun m hm => Nat.find_min h hm⟩
    · rename_i h
      exact False.elim (h hex)
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨n,i,hn,hminEq⟩ := hm
    obtain ⟨hp,hsmaller⟩ := hmin n i hn
    rw [hminEq] at hp hsmaller
    have hm0 : 0<m := hp.1
    by_cases hm1 : m=1
    · exact Or.inl ⟨0,by simpa [P] using hm1⟩
    · have hgrowth : ∀ k, k<P (k + 1) := by
        intro k
        induction k with
        | zero => norm_num [P]
        | succ k ih =>
          have hq := (by have hs := (pell_companion_step (k+1)).1; obtain ⟨j, hj⟩ := companion_odd (k+1); omega : P (k+1) < P (k+1 + 1))
          change k+1<P (k+1+1)
          omega
      have hex : ∃ k,m<P (k + 1) := ⟨m,hgrowth m⟩
      let j := Nat.find hex
      have hjQ : m<P (j + 1) := Nat.find_spec hex
      have hj0 : 0<j := by
        by_contra hz
        have hz' : j=0 := by omega
        rw [hz'] at hjQ
        norm_num [P] at hjQ
        omega
      let k := j-1
      have hkj : k+1=j := by dsimp [k];omega
      have hqle : P (k + 1)≤m := by
        have hh := Nat.find_min hex (show k<j by omega)
        omega
      have hmQ : m<P (k + 2) := by simpa [show k+2=j+1 by omega] using hjQ
      have hk1 : 1≤k := by
        by_contra hz
        have hz' : k=0 := by omega
        rw [hz'] at hmQ
        norm_num [P] at hmQ
        omega
      by_cases hmq : m=P (k + 1)
      · exact Or.inl ⟨k,hmq⟩
      · by_cases hm2 : m=2*P (k + 1)
        · exact Or.inr (Or.inl ⟨k,hm2⟩)
        · by_cases hmr : m=P (k + 1)+P k
          · exact Or.inr (Or.inr ⟨k,hk1,hmr⟩)
          · have hmn : m≤n := by
              by_contra hgt
              have hw : 0<(lowerMechanicalFactor silverSlope 0 n i).length := by
                simpa [lowerMechanicalFactor] using hn
              have hpn : AbelianPeriod (lowerMechanicalFactor silverSlope 0 n i) n := by
                simpa [lowerMechanicalFactor] using hlength _ hw
              exact hsmaller n (by omega) hpn
            have hnq : P (k + 1)<n := by omega
            have hnotq := hsmaller (P (k + 1)) (by omega)
            exact False.elim (silver_noncandidate_exclusion k n i m hk1
              hqle hmQ hmq hm2 hmr hnq hnotq hp)
  · intro m hm
    rcases hm with ⟨k,rfl⟩ | ⟨k,rfl⟩ | ⟨k,hk,rfl⟩
    · exact silver_q_realisation k
    · by_cases hk : k=0
      · subst k
        simpa [P,silverAbelianPeriodSet,abelianPeriodSet] using silver_q_realisation 1
      · have hw := silver_w2_min_period k (by omega)
        exact ⟨_,_,hw.1,hw.2⟩
    · have hw := silver_wr_min_period k hk
      exact ⟨_,_,hw.1,hw.2⟩
#print axioms result
end D5.S1.Words.Mechanical
