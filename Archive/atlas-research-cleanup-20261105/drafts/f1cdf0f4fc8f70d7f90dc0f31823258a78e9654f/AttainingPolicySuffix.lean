
/-- An explicit full-history policy implementing the finite attaining tree.
Its terminal label is the entire observed history, which the decoder consumes. -/
def attainingPolicy (A : Finset α) (x z y : Query A) (h : History A) :
    Sum (Query A) (History A) :=
  if h.length = 0 then .inl x
  else if h.length = 1 then .inl z
  else if h.length = 2 ∧ (candidateSet A h).card ≠ 1 then .inl y
  else .inr h

/-- Four units of fuel suffice for the actual three-query-or-earlier run,
including its terminal action. No hidden state enters the policy. -/
theorem attainingPolicy_execute (A : Finset α) (x z y : Query A) (C : Cycle α) :
    execute (read A) (attainingPolicy A x z y) 4 [] C =
      some (runPassiveProtocol (read A) (attainingProtocol A x z y) C,
        runPassiveProtocol (read A) (attainingProtocol A x z y) C) := by
  by_cases hp : (candidateSet A (pairHistory A x z (read A x C) (read A z C))).card = 1
  · simp only [attainingProtocol,runPassiveProtocol,if_pos hp]
    simpa [execute,attainingPolicy,pairHistory] using (show
      execute (read A) (attainingPolicy A x z y) 4 [] C =
      some ([⟨x,read A x C⟩,⟨z,read A z C⟩], [⟨x,read A x C⟩,⟨z,read A z C⟩]) from by
        simp [execute,attainingPolicy,show (candidateSet A
          [⟨x,read A x C⟩,⟨z,read A z C⟩]).card = 1 from hp])
  · simp only [attainingProtocol,runPassiveProtocol,if_neg hp]
    simpa [execute,attainingPolicy,pairHistory] using (show
      execute (read A) (attainingPolicy A x z y) 4 [] C =
      some ([⟨x,read A x C⟩,⟨z,read A z C⟩,⟨y,read A y C⟩],
        [⟨x,read A x C⟩,⟨z,read A z C⟩,⟨y,read A y C⟩]) from by
        simp [execute,attainingPolicy,show (candidateSet A
          [⟨x,read A x C⟩,⟨z,read A z C⟩]).card ≠ 1 from hp])
