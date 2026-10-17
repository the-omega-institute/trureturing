/- SOURCE ONLY. UNCOMPILED. Counts and paired kinds for the EXISTING reduce.
This does not strengthen Terminal by a new input hypothesis, and does not
replace reduce by a newly assumed or independently supplied paired chain. -/
import D5.S3.ConceptDynamics.Coding.SplitTowerPositiveAccounting
import D5.S3.ConceptDynamics.Coding.ResponseTwoSidedConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ConstructedTowerProfiles
open EssentialWordRealization FiniteWindowTableCriterion TwoSidedFiniteInduction
open OutSplitConjugacyDecrease (Code)
open SplitTowerPositiveAccounting TowerWord
open TypedPositiveSplitWord SplitTowerTranslation

/-- true means outgoing, false means incoming, in actual traversal order. -/
def kinds {F K : Presentation} : Tower F K → List Bool
  | .nil _ => []
  | .outgoing _ _ tail => true :: kinds tail
  | .incoming _ _ tail => false :: kinds tail

def Profile {F H : Presentation} {P : Hist F ≃ₜ Hist H} {k : ℕ}
    (r : Terminal F H P k) (M N : ℕ) : Prop :=
  inCount r.left = M ∧ outCount r.left = N ∧
  inCount r.right = M ∧ outCount r.right = N ∧ kinds r.left = kinds r.right

/-- The recursion itself certifies the pairing. Its incoming and outgoing
counts on EACH side are exactly the supplied inverse radii M and N. -/
theorem reduce_profile : ∀ (k : ℕ) (F H : Presentation) (c : Code F.graph H.graph)
    (P : Hist F ≃ₜ Hist H)
    (hP : ∀ x t, (P x).val t = c.edge (x.val t))
    (M N : ℕ) (Q : LegalWord H.graph (M+N+1) → F.E)
    (hQ : ∀ y t, Q (historyWindow H.graph y (t-(M:ℤ)) (M+N+1)) = (P.symm y).val t)
    (hk : M+N = k), Profile (reduce k F H c P hP M N Q hQ hk) M N := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro F H c P hP M N Q hQ hk
    cases N with
    | succ n =>
      let F' := out F H c.edge
      let H' := out H H id
      let c' : Code F'.graph H'.graph := OutSplitConjugacyDecrease.splitCode c
      let P' : Hist F' ≃ₜ Hist H' := OutSplitConjugacyDecrease.changed c P
      have hp' : ∀ x t, (P' x).val t = c'.edge (x.val t) :=
        OutSplitConjugacyDecrease.changed_one_block c P hP
      let Q' : LegalWord H'.graph (M+n+1) → F'.E :=
        OutSplitConjugacyDecrease.recover c P hP H.essential M n Q hQ
      have hq' : ∀ y t, Q' (historyWindow H'.graph y (t-(M:ℤ)) (M+n+1)) =
          (P'.symm y).val t :=
        OutSplitConjugacyDecrease.recover_window c P hP H.essential M n Q hQ
      let r := reduce (M+n) F' H' c' P' hp' M n Q' hq' rfl
      have hr : Profile r M n := ih (M+n) (by omega) F' H' c' P' hp' M n Q' hq' rfl
      unfold reduce
      rw [Nat.strongRecOn_eq]
      change inCount r.left = M ∧ outCount r.left+1 = n+1 ∧
        inCount r.right = M ∧ outCount r.right+1 = n+1 ∧
        true :: kinds r.left = true :: kinds r.right
      exact ⟨hr.1,congrArg (fun v => v+1) hr.2.1,hr.2.2.1,
        congrArg (fun v => v+1) hr.2.2.2.1,congrArg (List.cons true) hr.2.2.2.2⟩
    | zero =>
      cases M with
      | succ m =>
        let F' := TwoSidedFiniteInduction.incoming F H c.edge
        let H' := TwoSidedFiniteInduction.incoming H H id
        let c' : Code F'.graph H'.graph := InSplitConjugacyDecrease.splitCode c
        let P' : Hist F' ≃ₜ Hist H' := InSplitConjugacyDecrease.changed c P
        have hp' : ∀ x t, (P' x).val t = c'.edge (x.val t) :=
          InSplitConjugacyDecrease.changed_one_block c P hP
        let Q' : LegalWord H'.graph (m+0+1) → F'.E :=
          InSplitConjugacyDecrease.recover c P hP H.essential m 0 Q hQ
        have hq' : ∀ y t, Q' (historyWindow H'.graph y (t-(m:ℤ)) (m+0+1)) =
            (P'.symm y).val t :=
          InSplitConjugacyDecrease.recover_window c P hP H.essential m 0 Q hQ
        let r := reduce (m+0) F' H' c' P' hp' m 0 Q' hq' rfl
        have hr : Profile r m 0 := ih (m+0) (by omega) F' H' c' P' hp' m 0 Q' hq' rfl
        unfold reduce
        rw [Nat.strongRecOn_eq]
        change inCount r.left+1 = m+1 ∧ outCount r.left = 0 ∧
          inCount r.right+1 = m+1 ∧ outCount r.right = 0 ∧
          false :: kinds r.left = false :: kinds r.right
        exact ⟨congrArg (fun v => v+1) hr.1,hr.2.1,
          congrArg (fun v => v+1) hr.2.2.1,hr.2.2.2.1,
          congrArg (List.cons false) hr.2.2.2.2⟩
      | zero =>
        unfold reduce
        rw [Nat.strongRecOn_eq]
        exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The requested -k is now a conclusion for the constructed reduction,
not a law postulated for arbitrary towers of equal length. -/
theorem reduce_literal (k : ℕ) (F H : Presentation) (c : Code F.graph H.graph)
    (P : Hist F ≃ₜ Hist H) (hP : ∀ x t, (P x).val t = c.edge (x.val t))
    (M N : ℕ) (Q : LegalWord H.graph (M+N+1) → F.E)
    (hQ : ∀ y t, Q (historyWindow H.graph y (t-(M:ℤ)) (M+N+1)) = (P.symm y).val t)
    (hk : M+N = k) (x : Hist F) :
    P x = time H.graph (-(k:ℤ))
      ((terminalWord (reduce k F H c P hP M N Q hQ hk)).eval x) := by
  let r := reduce k F H c P hP M N Q hQ hk
  have hr := reduce_profile k F H c P hP M N Q hQ hk
  have he : -(inCount r.left : ℤ)-(outCount r.right : ℤ) = -(k:ℤ) := by
    rw [hr.1,hr.2.2.2.1]
    omega
  simpa only [he] using terminal_literal r x

section Response
open OriginalResponseNumbering ResponseOutSplitConsumer ResponseTwoSidedConsumer
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E) (hG : Essential G)
variable {a b c d : ℕ} (pair : TablePair G G a b c d) (S : SameTableConjugacy pair)

/-- Account for the completed FIRST outgoing step as well as reduce's tail. -/
theorem response_profile : Profile (terminal G hG pair S) (a+c) (b+d+1) := by
  let F := response G hG pair S
  let H := original G hG
  letI : TopologicalSpace H.E := H.topology
  letI : DiscreteTopology H.E := H.discrete
  let C := local_of_conjugacy hG hG pair S
  let cb := responseCode G pair C.seamG
  let P := numberedOutput G pair S C.seamG
  let F' := out F H cb.edge
  let H' := out H H id
  let cp := OutSplitConjugacyDecrease.splitCode cb
  let P' : Hist F' ≃ₜ Hist H' := splitOutput G pair hG S
  have hp' : ∀ x t, (P' x).val t = cp.edge (x.val t) := by
    apply OutSplitConjugacyDecrease.changed_one_block
    intro x t
    rfl
  let Q' : LegalWord H'.graph ((a+c)+(b+d)+1) → F'.E := splitRecover G pair hG S
  have hq' : ∀ y t, Q' (historyWindow H'.graph y (t-((a+c:ℕ):ℤ)) ((a+c)+(b+d)+1)) =
      (P'.symm y).val t := response_recovery G pair hG S
  let r := reduce ((a+c)+(b+d)) F' H' cp P' hp' (a+c) (b+d) Q' hq' rfl
  have hr : Profile r (a+c) (b+d) :=
    reduce_profile ((a+c)+(b+d)) F' H' cp P' hp' (a+c) (b+d) Q' hq' rfl
  change inCount r.left = a+c ∧ outCount r.left+1 = b+d+1 ∧
    inCount r.right = a+c ∧ outCount r.right+1 = b+d+1 ∧
    true :: kinds r.left = true :: kinds r.right
  exact ⟨hr.1,congrArg (fun v => v+1) hr.2.1,hr.2.2.1,
    congrArg (fun v => v+1) hr.2.2.2.1,congrArg (List.cons true) hr.2.2.2.2⟩
end Response
end D5.S3.ConceptDynamics.Coding.ConstructedTowerProfiles
