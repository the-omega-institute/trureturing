/- GID: D5/S3/Quantum/Dynamics/NativeReader/Fibers
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Fibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal decomposition of all extended paths into original source and legal tail. -/

import D5.S3.Quantum.Dynamics.NativeReader.Carrier

/-! All source and auxiliary coordinates of the complete extended carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader

/-- Restore the original tail at b10; no extended coordinate is discarded from the pair. -/
def originalPart (e : Extended) : Source :=
  ⟨fun k => if h : k.val < 10 then e.1 ⟨k.val, by omega⟩ else false, by
    refine ⟨by simpa using e.2.1, by simp, ?_⟩
    intro k
    by_cases hk : k.val < 9
    · simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, hk, show k.val < 10 by omega, show k.val + 1 < 10 by omega] using
        e.2.2.2 ⟨k.val, by omega⟩
    · have hv : k.val = 9 := by omega
      simp [hv, adjacent]⟩

def auxiliaryPart (e : Extended) : Tail ((originalPart e).1 9) :=
  ⟨fun k => if h : k.val < 6 then e.1 ⟨9 + k.val, by omega⟩ else true, by
    refine ⟨by simp [originalPart], by simp, ?_⟩
    intro k
    by_cases hk : k.val < 5
    · simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, show k.val < 6 by omega, show k.val + 1 < 6 by omega, Nat.add_assoc] using
        e.2.2.2 ⟨9 + k.val, by omega⟩
    · have hv : k.val = 5 := by omega
      have he : e.1 14 = false := e.2.2.1
      simp [hv, he, adjacent]⟩

/-- The complete dependent carrier, retaining both sectors and every complement path. -/
abbrev FiberCarrier := (q : Source) × Tail (q.1 9)

/-- Reinsert the actual five auxiliary sites; q remains the complete original source path. -/
def joinPath (i : Bool) (q : SourceSector i) (z : Tail i) : Extended :=
  ⟨fun k => if h : k.val < 10 then q.1.1 ⟨k.val, by omega⟩
      else z.1 ⟨k.val - 9, by omega⟩, by
    refine ⟨by simpa using q.1.2.1, ?_, ?_⟩
    · have hz := z.2.2.2 5
      have he : z.1 6 = true := z.2.2.1
      have hf : z.1 5 = false := by
        cases hb : z.1 5
        · rfl
        · simp [adjacent, he, hb] at hz
      simpa using hf
    · intro k
      by_cases hk : k.val < 9
      · simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, show k.val < 10 by omega, show k.val + 1 < 10 by omega] using
          q.1.2.2.2 ⟨k.val, by omega⟩
      · by_cases h9 : k.val = 9
        · have he : z.1 0 = q.1.1 9 := z.2.1.trans q.2.symm
          simpa [h9, he] using z.2.2.2 0
        · have hv : 10 ≤ k.val := by omega
          have hs : k.val + 1 - 9 = k.val - 9 + 1 := by omega
          simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, show ¬ k.val < 10 by omega, show ¬ k.val + 1 < 10 by omega, hs] using
            z.2.2.2 ⟨k.val - 9, by omega⟩⟩

theorem original_join (i : Bool) (q : SourceSector i) (z : Tail i) :
    originalPart (joinPath i q z) = q.1 := by
  apply Subtype.ext
  funext k
  by_cases hk : k.val < 10
  · simp [originalPart, joinPath, hk]
  · have hv : k = 10 := Fin.ext (by change k.val = 10; omega)
    subst k
    simpa [originalPart] using q.1.2.2.1.symm

theorem join_split (e : Extended) :
    joinPath ((originalPart e).1 9) ⟨originalPart e, rfl⟩ (auxiliaryPart e) = e := by
  apply Subtype.ext
  funext k
  by_cases hk : k.val < 10
  · simp [joinPath, originalPart, hk]
  · have hk6 : k.val - 9 < 6 := by omega
    have hadd : 9 + (k.val - 9) = k.val := by omega
    simp [joinPath, auxiliaryPart, hk, hk6, hadd]

/-- Both source sectors and every legal tail are represented without a dimension reduction. -/
def fullCarrierEquiv : Extended ≃ FiberCarrier where
  toFun e := ⟨originalPart e, auxiliaryPart e⟩
  invFun p := joinPath (p.1.1 9) ⟨p.1, rfl⟩ p.2
  left_inv := join_split
  right_inv p := by
    rcases p with ⟨q, z⟩
    apply Sigma.ext (original_join (q.1 9) ⟨q, rfl⟩ z)
    apply (Subtype.heq_iff_coe_eq (by
      intro v
      dsimp only
      rw [original_join])).mpr
    have hz6 : z.1 6 = true := z.2.2.1
    funext k
    fin_cases k <;> simp [auxiliaryPart, joinPath, originalPart, z.2.1, hz6]

end D5.S3.Quantum.Dynamics.NativeReader
