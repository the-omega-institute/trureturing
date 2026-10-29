/- GID: D5/S3/Quantum/Information/FivePartySSA
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FivePartySSA
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eleven actual conditional mutual informations give the quantum copy precursor. -/

import D5.S3.Quantum.Information.FivePartySSA.Marginals

set_option autoImplicit false

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Information.MarginalCalculus

namespace D5.S3.Quantum.Information.FivePartySSA

variable {A B C D E : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

/-- The eleven SSA terms are evaluated on marginals of one actual five-party density. -/
theorem eleven_cmi_nonnegative
    (rho : DensityState (A × (B × (C × (D × E))))) :
    0 ≤ -entropyA rho - entropyC rho - 2 * entropyD rho - entropyE rho - entropyAB rho + entropyAC rho + 2 * entropyAE rho + entropyBC rho + entropyBD rho + entropyCD rho + 2 * entropyDE rho - entropyACD rho - entropyBCD rho + 3 * entropyABCD rho - 3 * entropyABCDE rho := by

  have h1 : entropyABE rho + entropyE rho ≤
      entropyAE rho + entropyBE rho := by
    let e : (A × (E × B)) ≃ (A × (B × E)) :=
      { toFun := fun q => (q.1, (q.2.2, q.2.1))
        invFun := fun q => (q.1, (q.2.2, q.2.1))
        left_inv := by rintro ⟨a, ⟨e, b⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨b, e⟩⟩; rfl }

    have h := ssa_partition e (marginalABE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalABE rho)) = entropyE rho := by

      unfold marginalABE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitE
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro e; rfl
           right_inv := by rintro e; rfl })
        ({ toFun := fun q => (q.1.1, (q.1.2, (q.2.1, q.2.2)))
           invFun := fun q => ((q.1, q.2.1), (q.2.2.1, q.2.2.2))
           left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc A E B).trans e)
        (marginalABE rho)) = entropyAE rho := by

      unfold marginalABE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitAE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨a, e⟩; rfl
           right_inv := by rintro ⟨a, e⟩; rfl })
        ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
           invFun := fun q => (q.1, (q.2.1, q.2.2))
           left_inv := by rintro ⟨b, ⟨c, d⟩⟩; rfl
           right_inv := by rintro ⟨b, ⟨c, d⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm (E × B) A).trans e)
        (marginalABE rho)) = entropyBE rho := by

      unfold marginalABE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitBE
        ({ toFun := fun q => (q.2, q.1)
           invFun := fun q => (q.2, q.1)
           left_inv := by rintro ⟨e, b⟩; rfl
           right_inv := by rintro ⟨b, e⟩; rfl })
        ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
           invFun := fun q => (q.1, (q.2.1, q.2.2))
           left_inv := by rintro ⟨a, ⟨c, d⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨c, d⟩⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h2 : entropyACDE rho + entropyCE rho ≤
      entropyACE rho + entropyCDE rho := by
    let e : (A × ((C × E) × D)) ≃ (A × (C × (D × E))) :=
      { toFun := fun q => (q.1, (q.2.1.1, (q.2.2, q.2.1.2)))
        invFun := fun q => (q.1, ((q.2.1, q.2.2.2), q.2.2.1))
        left_inv := by rintro ⟨a, ⟨⟨c, e⟩, d⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨c, ⟨d, e⟩⟩⟩; rfl }

    have h := ssa_partition e (marginalACDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalACDE rho)) = entropyCE rho := by

      unfold marginalACDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitCE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨c, e⟩; rfl
           right_inv := by rintro ⟨c, e⟩; rfl })
        ({ toFun := fun q => (q.1.1, (q.2, q.1.2))
           invFun := fun q => ((q.1, q.2.2), q.2.1)
           left_inv := by rintro ⟨⟨a, d⟩, b⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, d⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc A (C × E) D).trans e)
        (marginalACDE rho)) = entropyACE rho := by

      unfold marginalACDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitACE
        ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
           invFun := fun q => (q.1, (q.2.1, q.2.2))
           left_inv := by rintro ⟨a, ⟨c, e⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨c, e⟩⟩; rfl })
        ({ toFun := fun q => (q.2, q.1)
           invFun := fun q => (q.2, q.1)
           left_inv := by rintro ⟨d, b⟩; rfl
           right_inv := by rintro ⟨b, d⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm ((C × E) × D) A).trans e)
        (marginalACDE rho)) = entropyCDE rho := by

      unfold marginalACDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitCDE
        ({ toFun := fun q => (q.1.1, (q.2, q.1.2))
           invFun := fun q => ((q.1, q.2.2), q.2.1)
           left_inv := by rintro ⟨⟨c, e⟩, d⟩; rfl
           right_inv := by rintro ⟨c, ⟨d, e⟩⟩; rfl })
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨a, b⟩; rfl
           right_inv := by rintro ⟨a, b⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h3 : entropyABCDE rho + entropyBCD rho ≤
      entropyABCD rho + entropyBCDE rho := by
    let e : (A × ((B × (C × D)) × E)) ≃ (A × (B × (C × (D × E)))) :=
      { toFun := fun q => (q.1, (q.2.1.1, (q.2.1.2.1, (q.2.1.2.2, q.2.2))))
        invFun := fun q => (q.1, ((q.2.1, (q.2.2.1, q.2.2.2.1)), q.2.2.2.2))
        left_inv := by rintro ⟨a, ⟨⟨b, ⟨c, d⟩⟩, e⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

    have h := ssa_partition e (marginalABCDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalABCDE rho)) = entropyBCD rho := by

      refine entropy_reduceState_congr _ splitBCD
        ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
           invFun := fun q => (q.1, (q.2.1, q.2.2))
           left_inv := by rintro ⟨b, ⟨c, d⟩⟩; rfl
           right_inv := by rintro ⟨b, ⟨c, d⟩⟩; rfl })
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨a, e⟩; rfl
           right_inv := by rintro ⟨a, e⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc A (B × (C × D)) E).trans e)
        (marginalABCDE rho)) = entropyABCD rho := by

      refine entropy_reduceState_congr _ splitABCD
        ({ toFun := fun q => (q.1, (q.2.1, (q.2.2.1, q.2.2.2)))
           invFun := fun q => (q.1, (q.2.1, (q.2.2.1, q.2.2.2)))
           left_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl })
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro e; rfl
           right_inv := by rintro e; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm ((B × (C × D)) × E) A).trans e)
        (marginalABCDE rho)) = entropyBCDE rho := by

      refine entropy_reduceState_congr _ splitBCDE
        ({ toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
           invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), q.2.2.2)
           left_inv := by rintro ⟨⟨b, ⟨c, d⟩⟩, e⟩; rfl
           right_inv := by rintro ⟨b, ⟨c, ⟨d, e⟩⟩⟩; rfl })
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro a; rfl
           right_inv := by rintro a; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h4 : entropyBCE rho + entropyC rho ≤
      entropyBC rho + entropyCE rho := by
    let e : (B × (C × E)) ≃ (B × (C × E)) :=
      { toFun := fun q => (q.1, (q.2.1, q.2.2))
        invFun := fun q => (q.1, (q.2.1, q.2.2))
        left_inv := by rintro ⟨b, ⟨c, e⟩⟩; rfl
        right_inv := by rintro ⟨b, ⟨c, e⟩⟩; rfl }

    have h := ssa_partition e (marginalBCE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalBCE rho)) = entropyC rho := by

      unfold marginalBCE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitC
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro c; rfl
           right_inv := by rintro c; rfl })
        ({ toFun := fun q => (q.2.1, (q.1.1, (q.2.2, q.1.2)))
           invFun := fun q => ((q.2.1, q.2.2.2), (q.1, q.2.2.1))
           left_inv := by rintro ⟨⟨b, e⟩, ⟨a, d⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨d, e⟩⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc B C E).trans e)
        (marginalBCE rho)) = entropyBC rho := by

      unfold marginalBCE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitBC
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨b, c⟩; rfl
           right_inv := by rintro ⟨b, c⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.2.2, q.1))
           invFun := fun q => (q.2.2, (q.1, q.2.1))
           left_inv := by rintro ⟨e, ⟨a, d⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨d, e⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm (C × E) B).trans e)
        (marginalBCE rho)) = entropyCE rho := by

      unfold marginalBCE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitCE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨c, e⟩; rfl
           right_inv := by rintro ⟨c, e⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.1, q.2.2))
           invFun := fun q => (q.2.1, (q.1, q.2.2))
           left_inv := by rintro ⟨b, ⟨a, d⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, d⟩⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h5 : entropyBDE rho + entropyD rho ≤
      entropyBD rho + entropyDE rho := by
    let e : (B × (D × E)) ≃ (B × (D × E)) :=
      { toFun := fun q => (q.1, (q.2.1, q.2.2))
        invFun := fun q => (q.1, (q.2.1, q.2.2))
        left_inv := by rintro ⟨b, ⟨d, e⟩⟩; rfl
        right_inv := by rintro ⟨b, ⟨d, e⟩⟩; rfl }

    have h := ssa_partition e (marginalBDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalBDE rho)) = entropyD rho := by

      unfold marginalBDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitD
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro d; rfl
           right_inv := by rintro d; rfl })
        ({ toFun := fun q => (q.2.1, (q.1.1, (q.2.2, q.1.2)))
           invFun := fun q => ((q.2.1, q.2.2.2), (q.1, q.2.2.1))
           left_inv := by rintro ⟨⟨b, e⟩, ⟨a, c⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, e⟩⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc B D E).trans e)
        (marginalBDE rho)) = entropyBD rho := by

      unfold marginalBDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitBD
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨b, d⟩; rfl
           right_inv := by rintro ⟨b, d⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.2.2, q.1))
           invFun := fun q => (q.2.2, (q.1, q.2.1))
           left_inv := by rintro ⟨e, ⟨a, c⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨c, e⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm (D × E) B).trans e)
        (marginalBDE rho)) = entropyDE rho := by

      unfold marginalBDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitDE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨d, e⟩; rfl
           right_inv := by rintro ⟨d, e⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.1, q.2.2))
           invFun := fun q => (q.2.1, (q.1, q.2.2))
           left_inv := by rintro ⟨b, ⟨a, c⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h6 : entropyABCDE rho + entropyACD rho ≤
      entropyABCD rho + entropyACDE rho := by
    let e : (B × ((A × (C × D)) × E)) ≃ (A × (B × (C × (D × E)))) :=
      { toFun := fun q => (q.2.1.1, (q.1, (q.2.1.2.1, (q.2.1.2.2, q.2.2))))
        invFun := fun q => (q.2.1, ((q.1, (q.2.2.1, q.2.2.2.1)), q.2.2.2.2))
        left_inv := by rintro ⟨b, ⟨⟨a, ⟨c, d⟩⟩, e⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

    have h := ssa_partition e (marginalABCDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalABCDE rho)) = entropyACD rho := by

      refine entropy_reduceState_congr _ splitACD
        ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
           invFun := fun q => (q.1, (q.2.1, q.2.2))
           left_inv := by rintro ⟨a, ⟨c, d⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨c, d⟩⟩; rfl })
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨b, e⟩; rfl
           right_inv := by rintro ⟨b, e⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc B (A × (C × D)) E).trans e)
        (marginalABCDE rho)) = entropyABCD rho := by

      refine entropy_reduceState_congr _ splitABCD
        ({ toFun := fun q => (q.2.1, (q.1, (q.2.2.1, q.2.2.2)))
           invFun := fun q => (q.2.1, (q.1, (q.2.2.1, q.2.2.2)))
           left_inv := by rintro ⟨b, ⟨a, ⟨c, d⟩⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl })
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro e; rfl
           right_inv := by rintro e; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm ((A × (C × D)) × E) B).trans e)
        (marginalABCDE rho)) = entropyACDE rho := by

      refine entropy_reduceState_congr _ splitACDE
        ({ toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
           invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), q.2.2.2)
           left_inv := by rintro ⟨⟨a, ⟨c, d⟩⟩, e⟩; rfl
           right_inv := by rintro ⟨a, ⟨c, ⟨d, e⟩⟩⟩; rfl })
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro b; rfl
           right_inv := by rintro b; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h7 : entropyBCDE rho + entropyBE rho ≤
      entropyBCE rho + entropyBDE rho := by
    let e : (C × ((B × E) × D)) ≃ (B × (C × (D × E))) :=
      { toFun := fun q => (q.2.1.1, (q.1, (q.2.2, q.2.1.2)))
        invFun := fun q => (q.2.1, ((q.1, q.2.2.2), q.2.2.1))
        left_inv := by rintro ⟨c, ⟨⟨b, e⟩, d⟩⟩; rfl
        right_inv := by rintro ⟨b, ⟨c, ⟨d, e⟩⟩⟩; rfl }

    have h := ssa_partition e (marginalBCDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalBCDE rho)) = entropyBE rho := by

      unfold marginalBCDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitBE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨b, e⟩; rfl
           right_inv := by rintro ⟨b, e⟩; rfl })
        ({ toFun := fun q => (q.2, (q.1.1, q.1.2))
           invFun := fun q => ((q.2.1, q.2.2), q.1)
           left_inv := by rintro ⟨⟨c, d⟩, a⟩; rfl
           right_inv := by rintro ⟨a, ⟨c, d⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc C (B × E) D).trans e)
        (marginalBCDE rho)) = entropyBCE rho := by

      unfold marginalBCDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitBCE
        ({ toFun := fun q => (q.2.1, (q.1, q.2.2))
           invFun := fun q => (q.2.1, (q.1, q.2.2))
           left_inv := by rintro ⟨c, ⟨b, e⟩⟩; rfl
           right_inv := by rintro ⟨b, ⟨c, e⟩⟩; rfl })
        ({ toFun := fun q => (q.2, q.1)
           invFun := fun q => (q.2, q.1)
           left_inv := by rintro ⟨d, a⟩; rfl
           right_inv := by rintro ⟨a, d⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm ((B × E) × D) C).trans e)
        (marginalBCDE rho)) = entropyBDE rho := by

      unfold marginalBCDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitBDE
        ({ toFun := fun q => (q.1.1, (q.2, q.1.2))
           invFun := fun q => ((q.1, q.2.2), q.2.1)
           left_inv := by rintro ⟨⟨b, e⟩, d⟩; rfl
           right_inv := by rintro ⟨b, ⟨d, e⟩⟩; rfl })
        ({ toFun := fun q => (q.2, q.1)
           invFun := fun q => (q.2, q.1)
           left_inv := by rintro ⟨c, a⟩; rfl
           right_inv := by rintro ⟨a, c⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h8 : entropyACE rho + entropyA rho ≤
      entropyAC rho + entropyAE rho := by
    let e : (C × (A × E)) ≃ (A × (C × E)) :=
      { toFun := fun q => (q.2.1, (q.1, q.2.2))
        invFun := fun q => (q.2.1, (q.1, q.2.2))
        left_inv := by rintro ⟨c, ⟨a, e⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨c, e⟩⟩; rfl }

    have h := ssa_partition e (marginalACE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalACE rho)) = entropyA rho := by

      unfold marginalACE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitA
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro a; rfl
           right_inv := by rintro a; rfl })
        ({ toFun := fun q => (q.2.1, (q.1.1, (q.2.2, q.1.2)))
           invFun := fun q => ((q.2.1, q.2.2.2), (q.1, q.2.2.1))
           left_inv := by rintro ⟨⟨c, e⟩, ⟨b, d⟩⟩; rfl
           right_inv := by rintro ⟨b, ⟨c, ⟨d, e⟩⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc C A E).trans e)
        (marginalACE rho)) = entropyAC rho := by

      unfold marginalACE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitAC
        ({ toFun := fun q => (q.2, q.1)
           invFun := fun q => (q.2, q.1)
           left_inv := by rintro ⟨c, a⟩; rfl
           right_inv := by rintro ⟨a, c⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.2.2, q.1))
           invFun := fun q => (q.2.2, (q.1, q.2.1))
           left_inv := by rintro ⟨e, ⟨b, d⟩⟩; rfl
           right_inv := by rintro ⟨b, ⟨d, e⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm (A × E) C).trans e)
        (marginalACE rho)) = entropyAE rho := by

      unfold marginalACE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitAE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨a, e⟩; rfl
           right_inv := by rintro ⟨a, e⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.1, q.2.2))
           invFun := fun q => (q.2.1, (q.1, q.2.2))
           left_inv := by rintro ⟨c, ⟨b, d⟩⟩; rfl
           right_inv := by rintro ⟨b, ⟨c, d⟩⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h9 : entropyABCE rho + entropyAB rho ≤
      entropyABC rho + entropyABE rho := by
    let e : (C × ((A × B) × E)) ≃ (A × (B × (C × E))) :=
      { toFun := fun q => (q.2.1.1, (q.2.1.2, (q.1, q.2.2)))
        invFun := fun q => (q.2.2.1, ((q.1, q.2.1), q.2.2.2))
        left_inv := by rintro ⟨c, ⟨⟨a, b⟩, e⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨b, ⟨c, e⟩⟩⟩; rfl }

    have h := ssa_partition e (marginalABCE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalABCE rho)) = entropyAB rho := by

      unfold marginalABCE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitAB
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨a, b⟩; rfl
           right_inv := by rintro ⟨a, b⟩; rfl })
        ({ toFun := fun q => (q.1.1, (q.2, q.1.2))
           invFun := fun q => ((q.1, q.2.2), q.2.1)
           left_inv := by rintro ⟨⟨c, e⟩, d⟩; rfl
           right_inv := by rintro ⟨c, ⟨d, e⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc C (A × B) E).trans e)
        (marginalABCE rho)) = entropyABC rho := by

      unfold marginalABCE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitABC
        ({ toFun := fun q => (q.2.1, (q.2.2, q.1))
           invFun := fun q => (q.2.2, (q.1, q.2.1))
           left_inv := by rintro ⟨c, ⟨a, b⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl })
        ({ toFun := fun q => (q.2, q.1)
           invFun := fun q => (q.2, q.1)
           left_inv := by rintro ⟨e, d⟩; rfl
           right_inv := by rintro ⟨d, e⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm ((A × B) × E) C).trans e)
        (marginalABCE rho)) = entropyABE rho := by

      unfold marginalABCE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitABE
        ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
           invFun := fun q => ((q.1, q.2.1), q.2.2)
           left_inv := by rintro ⟨⟨a, b⟩, e⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, e⟩⟩; rfl })
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨c, d⟩; rfl
           right_inv := by rintro ⟨c, d⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h10 : entropyCDE rho + entropyD rho ≤
      entropyCD rho + entropyDE rho := by
    let e : (C × (D × E)) ≃ (C × (D × E)) :=
      { toFun := fun q => (q.1, (q.2.1, q.2.2))
        invFun := fun q => (q.1, (q.2.1, q.2.2))
        left_inv := by rintro ⟨c, ⟨d, e⟩⟩; rfl
        right_inv := by rintro ⟨c, ⟨d, e⟩⟩; rfl }

    have h := ssa_partition e (marginalCDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalCDE rho)) = entropyD rho := by

      unfold marginalCDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitD
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro d; rfl
           right_inv := by rintro d; rfl })
        ({ toFun := fun q => (q.2.1, (q.2.2, (q.1.1, q.1.2)))
           invFun := fun q => ((q.2.2.1, q.2.2.2), (q.1, q.2.1))
           left_inv := by rintro ⟨⟨c, e⟩, ⟨a, b⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, e⟩⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc C D E).trans e)
        (marginalCDE rho)) = entropyCD rho := by

      unfold marginalCDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitCD
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨c, d⟩; rfl
           right_inv := by rintro ⟨c, d⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.2.2, q.1))
           invFun := fun q => (q.2.2, (q.1, q.2.1))
           left_inv := by rintro ⟨e, ⟨a, b⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, e⟩⟩; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm (D × E) C).trans e)
        (marginalCDE rho)) = entropyDE rho := by

      unfold marginalCDE
      rw [reduceState_compose]

      refine entropy_reduceState_congr _ splitDE
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨d, e⟩; rfl
           right_inv := by rintro ⟨d, e⟩; rfl })
        ({ toFun := fun q => (q.2.1, (q.2.2, q.1))
           invFun := fun q => (q.2.2, (q.1, q.2.1))
           left_inv := by rintro ⟨c, ⟨a, b⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  have h11 : entropyABCDE rho + entropyABC rho ≤
      entropyABCD rho + entropyABCE rho := by
    let e : (D × ((A × (B × C)) × E)) ≃ (A × (B × (C × (D × E)))) :=
      { toFun := fun q => (q.2.1.1, (q.2.1.2.1, (q.2.1.2.2, (q.1, q.2.2))))
        invFun := fun q => (q.2.2.2.1, ((q.1, (q.2.1, q.2.2.1)), q.2.2.2.2))
        left_inv := by rintro ⟨d, ⟨⟨a, ⟨b, c⟩⟩, e⟩⟩; rfl
        right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

    have h := ssa_partition e (marginalABCDE rho)

    have hc : vonNeumannEntropy (reduceState (centerSplit.trans e)
        (marginalABCDE rho)) = entropyABC rho := by

      refine entropy_reduceState_congr _ splitABC
        ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
           invFun := fun q => (q.1, (q.2.1, q.2.2))
           left_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl })
        ({ toFun := fun q => (q.1, q.2)
           invFun := fun q => (q.1, q.2)
           left_inv := by rintro ⟨d, e⟩; rfl
           right_inv := by rintro ⟨d, e⟩; rfl }) rho ?_
      intro q
      rfl

    have hl : vonNeumannEntropy (reduceState ((Equiv.prodAssoc D (A × (B × C)) E).trans e)
        (marginalABCDE rho)) = entropyABCD rho := by

      refine entropy_reduceState_congr _ splitABCD
        ({ toFun := fun q => (q.2.1, (q.2.2.1, (q.2.2.2, q.1)))
           invFun := fun q => (q.2.2.2, (q.1, (q.2.1, q.2.2.1)))
           left_inv := by rintro ⟨d, ⟨a, ⟨b, c⟩⟩⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl })
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro e; rfl
           right_inv := by rintro e; rfl }) rho ?_
      intro q
      rfl

    have hr : vonNeumannEntropy (reduceState ((Equiv.prodComm ((A × (B × C)) × E) D).trans e)
        (marginalABCDE rho)) = entropyABCE rho := by

      refine entropy_reduceState_congr _ splitABCE
        ({ toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
           invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), q.2.2.2)
           left_inv := by rintro ⟨⟨a, ⟨b, c⟩⟩, e⟩; rfl
           right_inv := by rintro ⟨a, ⟨b, ⟨c, e⟩⟩⟩; rfl })
        ({ toFun := fun q => q
           invFun := fun q => q
           left_inv := by rintro d; rfl
           right_inv := by rintro d; rfl }) rho ?_
      intro q
      rfl

    rwa [hc, hl, hr] at h

  linarith

#print axioms eleven_cmi_nonnegative

end D5.S3.Quantum.Information.FivePartySSA
