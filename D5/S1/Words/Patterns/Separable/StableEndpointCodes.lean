/- GID: D5/S1/Words/Patterns/Separable/StableEndpointCodes
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/StableEndpointCodes
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed bounded endpoint codes reconstruct actual histories and restricted fibers. -/

import D5.S1.Words.Patterns.Separable.CappedExploration

/-!
Only bounded endpoint shapes and stop kinds are stored. The terminal permutation
is not part of a code. Sizes, states and literal value offsets are reconstructed
at each actual length. All lengths and bounds are symbolic and unbounded.
-/

namespace D5.S1.Words.Patterns.Separable.StableEndpointCodes

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
open D5.S1.Words.Patterns.Separable.CappedExploration

instance : Fintype StopKind :=
  ⟨{.good, .short, .small, .exhausted, .cap}, by intro kind; cases kind <;> simp⟩

inductive Code (K : ℕ) : ℕ → Type where
  | stop {H} (kind : StopKind) : Code K H
  | emit {H} (sign : Bool) (size : Fin K) (shape : Indecomposable sign (size.val + 1))
      (tail : Code K H) : Code K (H + 1)
  | discard {H} (sign : Bool) (size : Fin K) (shape : Avoider (size.val + 1))
      (tail : Code K H) : Code K (H + 1)

instance (K H : ℕ) : Finite (Code K H) := by
  induction H with
  | zero =>
    exact Finite.of_injective (fun code => match code with | .stop kind => kind)
      (by intro first last equality; cases first; cases last; cases equality; rfl)
  | succ H induction =>
    haveI := induction
    let target := StopKind ⊕
      ((Σ sign : Bool, Σ size : Fin K, Indecomposable sign (size.val + 1) × Code K H) ⊕
       (Σ sign : Bool, Σ size : Fin K, Avoider (size.val + 1) × Code K H))
    let encode : Code K (H + 1) → target
      | .stop kind => .inl kind
      | .emit sign size shape tail => .inr (.inl ⟨sign, size, shape, tail⟩)
      | .discard sign size shape tail => .inr (.inr ⟨sign, size, shape, tail⟩)
    exact Finite.of_injective encode (by
      intro first last equality
      cases first <;> cases last <;> simp_all [encode, target]
      · rcases equality with ⟨rfl, rest⟩
        cases eq_of_heq rest
        simp
      · rcases equality with ⟨rfl, rfl, rest⟩
        cases eq_of_heq rest
        simp)

noncomputable instance (K H : ℕ) : Fintype (Code K H) := Fintype.ofFinite _

def Legal {K} : {H : ℕ} → Option Bool → ℕ → Code K H → Prop
  | H, _, m, .stop kind =>
      (m = 0 ∧ kind = .good) ∨
      (0 < m ∧ ((H = 0 ∧ kind = .exhausted) ∨ (0 < H ∧ kind = .cap)))
  | _, state, m, .emit sign size _ tail =>
      0 < m ∧ (state = none ∨ state = some (!sign)) ∧ Legal none (m - (size.val + 1)) tail
  | _, state, m, .discard sign _ _ tail =>
      0 < m ∧ (state = none ∨ state = some (!sign)) ∧ Legal (some sign) m tail

abbrev StableCode (state : Option Bool) (m K H : ℕ) :=
  {code : Code K H // Legal state m code}

def Compatible {K H} (state : Option Bool) : Code K H → Prop
  | .stop _ => True
  | .emit sign _ _ tail =>
      (state = none ∨ state = some (!sign)) ∧ Compatible none tail
  | .discard sign _ _ tail =>
      (state = none ∨ state = some (!sign)) ∧ Compatible (some sign) tail

def admissible {K H state m} {code : Code K H} (legal : Legal state m code) :
    Compatible state code :=
  match code with
  | .stop _ => trivial
  | .emit _ _ _ _ => ⟨legal.2.1, admissible legal.2.2⟩
  | .discard _ _ _ _ => ⟨legal.2.1, admissible legal.2.2⟩

def terminal {K H} : Code K H → StopKind
  | .stop kind => kind
  | .emit _ _ _ tail => terminal tail
  | .discard _ _ _ tail => terminal tail

def word {K H} (code : Code K H) (alphabet low : ℕ) : List (Option (Fin alphabet)) :=
  match code with
  | .stop _ => []
  | .emit sign size shape tail =>
      (if sign then List.replicate (size.val + 1) none
        else List.ofFn (fun position => EndpointHistory.label alphabet
          (low + (shape.val.val position).val))) ++
        word tail alphabet (low + if sign then 0 else size.val + 1)
  | .discard sign size _ tail =>
      word tail alphabet (low + if sign then size.val + 1 else 0)

def decode {K H} (code : Code K H) {state} (valid : Compatible state code)
    (n : ℕ) (large : H * K < n) : EndpointHistory state n :=
  match code with
    | .stop kind => .stop state n
    | @Code.emit _ H sign size shape tail => by
      have compatible := valid.1
      have childValid := valid.2
      have bound := size.isLt
      have childLarge : H * K < n - (size.val + 1) := by
        rw [Nat.succ_mul] at large
        omega
      have positive : 0 < n - (size.val + 1) := by omega
      have equality : size.val + 1 + (n - (size.val + 1)) = n := by
        rw [Nat.succ_mul] at large
        omega
      exact equality ▸ EndpointHistory.emit sign (by omega) positive compatible shape
        (decode tail childValid _ childLarge)
    | @Code.discard _ H sign size shape tail => by
      have compatible := valid.1
      have childValid := valid.2
      have bound := size.isLt
      have childLarge : H * K < n - (size.val + 1) := by
        rw [Nat.succ_mul] at large
        omega
      have positive : 0 < n - (size.val + 1) := by omega
      have equality : (n - (size.val + 1)) + (size.val + 1) = n := by
        rw [Nat.succ_mul] at large
        omega
      exact equality ▸ EndpointHistory.discard sign positive (by omega) compatible shape
        (decode tail childValid _ childLarge)

abbrev history {K H state m} (code : StableCode state m K H) (n : ℕ)
    (large : H * K < n) : EndpointHistory state n := decode code.val (admissible code.property) n large

def compress {state n} (supplied : EndpointHistory state n) (kind : StopKind)
    (K : ℕ) : (H : ℕ) → Option (Code K H)
  | 0 => match supplied with | .stop _ _ => some (.stop kind) | _ => none
  | H + 1 =>
    match supplied with
    | .stop _ _ => some (.stop kind)
    | .emit (left := left) sign hl _ _ shape tail =>
      if bounded : left ≤ K then
        let size : Fin K := ⟨left - 1, by omega⟩
        have equality : size.val + 1 = left := by dsimp [size]; omega
        (compress tail kind K H).map (.emit sign size (equality.symm ▸ shape))
      else none
    | .discard (right := right) sign _ hr _ shape tail =>
      if bounded : right ≤ K then
        let size : Fin K := ⟨right - 1, by omega⟩
        have equality : size.val + 1 = right := by dsimp [size]; omega
        (compress tail kind K H).map (.discard sign size (equality.symm ▸ shape))
      else none

noncomputable def codeStep {state n} (m B K H : ℕ)
    (large : (H + 1) * K + max (2 * K) (max m B) < n) (positive : 0 < m)
    (π : Carrier state n) (factors : Recovered π)
    (continuation : ∀ {root size} (target : ℕ),
      H * K + max (2 * K) (max target B) < size →
        Carrier root size → StableCode root target K H) : StableCode state m K (H + 1) := by
    classical
    have sizeEq := factors.sum_eq
    have parent := large
    rw [Nat.succ_mul] at parent
    by_cases hl : factors.left ≤ K
    · let size : Fin K := ⟨factors.left - 1, by have := factors.left_pos; omega⟩
      have sizeEq' : size.val + 1 = factors.left := by
        have := factors.left_pos
        dsimp [size]
        omega
      have childLarge : H * K + max (2 * K) (max (m - factors.left) B) < factors.right := by
        have smaller : max (2 * K) (max (m - factors.left) B) ≤
            max (2 * K) (max m B) := max_le_max_left _ (max_le_max_right _ (Nat.sub_le _ _))
        omega
      let child := continuation (root := none) (size := factors.right)
        (m - factors.left) childLarge ⟨factors.last, trivial⟩
      exact ⟨.emit factors.sign size (sizeEq'.symm ▸ factors.first) child.val,
        by simpa only [Legal, sizeEq'] using
          And.intro (show 0 < m by omega) (And.intro factors.compatible child.property)⟩
    by_cases hr : factors.right ≤ K
    · let size : Fin K := ⟨factors.right - 1, by have := factors.right_pos; omega⟩
      have sizeEq' : size.val + 1 = factors.right := by
        have := factors.right_pos
        dsimp [size]
        omega
      have childLarge : H * K + max (2 * K) (max m B) < factors.left := by omega
      let child := continuation (root := some factors.sign) (size := factors.left)
        m childLarge factors.first
      exact ⟨.discard factors.sign size (sizeEq'.symm ▸ factors.last) child.val,
        ⟨by omega, factors.compatible, child.property⟩⟩
    · exact ⟨.stop .cap, Or.inr ⟨by omega, Or.inr ⟨by omega, rfl⟩⟩⟩

noncomputable def boundedClassify {state n} (m B K : ℕ) :
    (H : ℕ) → H * K + max (2 * K) (max m B) < n → Carrier state n → StableCode state m K H
  | 0, large, π => by
    classical
    by_cases hm : m = 0
    · exact ⟨.stop .good, Or.inl ⟨hm, rfl⟩⟩
    · exact ⟨.stop .exhausted, Or.inr ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩⟩
  | H + 1, large, π => by
    classical
    by_cases hm : m = 0
    · exact ⟨.stop .good, Or.inl ⟨hm, rfl⟩⟩
    have hn : 2 ≤ n := by
      have : m ≤ max (2 * K) (max m B) := le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    exact codeStep m B K H large (by omega) π (recover π hn)
      (fun target childLarge child => boundedClassify target B K H childLarge child)

theorem stable_success_fibers (K H : ℕ) :
    ∀ (state : Option Bool) (m B n : ℕ)
      (large : H * K + max (2 * K) (max m B) < n)
      (code : StableCode state m K H), terminal code.val = .good →
      ∀ π : Avoider n,
        Fiber m B H K (history code n (by omega), .good) π ↔
          (history code n (by omega)).Event π := by
  classical
  have inverse {state left right} (sign : Bool) (hl : 0 < left) (hr : 0 < right)
      (α : Indecomposable sign left) (β : Avoider right)
      (π : Carrier state (left + right))
      (assembled : blockSum sign α.val.val β.val = π.val.val)
      (minimum : MinimumCut sign π.val.val left) :
      let recovered := recover π (by omega)
      recovered.sign = sign ∧ recovered.left = left ∧ recovered.right = right ∧
        HEq recovered.first α ∧ HEq recovered.last β := by
    dsimp only
    obtain ⟨s, a, b, ha, hb, sumEq, compatible, first, last, reconstruction,
      mincut, unique, factorUnique⟩ := recover π (by omega)
    dsimp only at *
    obtain ⟨sameSign, sameLeft⟩ := unique sign left hl (by omega) minimum
    subst s
    subst a
    have sameRight : b = right := by omega
    subst b
    have factors := factorUnique α β (assembled.trans (congrArg Subtype.val reconstruction).symm)
    exact ⟨rfl, rfl, rfl, heq_of_eq factors.1.symm, heq_of_eq factors.2.symm⟩
  have roundtrip : ∀ (H : ℕ) (state : Option Bool) (m B n : ℕ)
      (large : H * K + max (2 * K) (max m B) < n)
      (code : StableCode state m K H), terminal code.val = .good →
      ∀ sample : (history code n (by omega)).Leaf,
        CappedExploration.classify m B H K
          ⟨(history code n (by omega)).assemble sample,
            ((endpoint_history_count_kernel _).1 sample).1⟩ =
          (history code n (by omega), .good) := by
    intro H
    induction H with
    | zero =>
      intro state m B n large code good sample
      rcases code with ⟨code, legal⟩
      cases code with
      | stop kind =>
        simp only [terminal] at good
        subst kind
        have hm : m = 0 := by simpa [Legal] using legal
        subst m
        have hb : B < n := by omega
        simp [history, decode, CappedExploration.classify, explore, Nat.recAux, hb]
    | succ H induction =>
      intro state m B n large code good sample
      rcases code with ⟨code, legal⟩
      cases code with
      | stop kind =>
        simp only [terminal] at good
        subst kind
        have hm : m = 0 := by simpa [Legal] using legal
        subst m
        have hb : B < n := by omega
        simp [history, decode, CappedExploration.classify, explore, Nat.recAux, hb]
      | emit sign size shape tail =>
        have hm := legal.1
        have compatible := legal.2.1
        have childLegal := legal.2.2
        have bound := size.isLt
        have parent := large
        rw [Nat.succ_mul] at parent
        generalize rightEq : n - (size.val + 1) = right
        have nEq : n = size.val + 1 + right := by omega
        have childLarge : H * K + max (2 * K) (max (m - (size.val + 1)) B) < right := by
          have smaller : max (2 * K) (max (m - (size.val + 1)) B) ≤
              max (2 * K) (max m B) :=
            max_le_max_left _ (max_le_max_right _ (Nat.sub_le _ _))
          omega
        let child : StableCode none (m - (size.val + 1)) K H := ⟨tail, childLegal⟩
        have ih := induction none (m - (size.val + 1)) B right childLarge child good
        subst n
        let childHistory := history child right (by omega)
        let parentHistory := EndpointHistory.emit sign (by omega)
          (show 0 < right by omega) compatible shape childHistory
        have decoded : history ⟨.emit sign size shape tail, legal⟩
            (size.val + 1 + right) (by omega) = parentHistory := by
          dsimp only [history, decode]
          apply eq_of_heq
          apply HEq.trans (eqRec_heq _ _)
          congr 2 <;> simp [history, childHistory, child]
        revert sample
        rw [decoded]
        intro sample
        let π : Carrier state (size.val + 1 + right) :=
          ⟨parentHistory.assemble sample, ((endpoint_history_count_kernel parentHistory).1 sample).1⟩
        change CappedExploration.classify m B (H + 1) K π = (parentHistory, .good)
        simp only [CappedExploration.classify, explore, Nat.recAux,
          dif_neg (show m ≠ 0 by omega), dif_neg (show ¬size.val + 1 + right < 2 by omega)]
        have inv := inverse sign (show 0 < size.val + 1 by omega)
          (show 0 < right by omega) shape (childHistory.assemble sample) π rfl
          ((endpoint_history_count_kernel parentHistory).1 sample).2.1
        generalize hr : recover π (by omega) = recovered at inv ⊢
        rcases recovered with ⟨s, a, b, ha, hb, eq, compat, first, last,
          reconstruction, mincut, unique, factorUnique⟩
        dsimp only at inv
        rcases inv with ⟨hs, haEq, hbEq, hfirst, hlast⟩
        subst s
        subst a
        subst b
        cases hfirst
        cases hlast
        have hsmall : ¬size.val + 1 + right < 2 := by omega
        have hcap : size.val + 1 ≤ K := by omega
        have ichild := ih sample
        have ihistory := congrArg Prod.fst ichild
        have ikind := congrArg Prod.snd ichild
        change (explore (state := none) (m - (size.val + 1)) B K H
          ⟨childHistory.assemble sample, trivial⟩).history = childHistory at ihistory
        change (explore (state := none) (m - (size.val + 1)) B K H
          ⟨childHistory.assemble sample, trivial⟩).kind = .good at ikind
        simp only [dif_pos hcap]
        change (EndpointHistory.emit sign _ _ compatible shape
          (explore (state := none) (m - (size.val + 1)) B K H
            ⟨childHistory.assemble sample, trivial⟩).history,
          (explore (state := none) (m - (size.val + 1)) B K H
            ⟨childHistory.assemble sample, trivial⟩).kind) = (parentHistory, .good)
        rw [ihistory, ikind]
      | discard sign size shape tail =>
        have hm := legal.1
        have compatible := legal.2.1
        have childLegal := legal.2.2
        have bound := size.isLt
        have parent := large
        rw [Nat.succ_mul] at parent
        generalize leftEq : n - (size.val + 1) = left
        have nEq : n = left + (size.val + 1) := by omega
        have childLarge : H * K + max (2 * K) (max m B) < left := by omega
        let child : StableCode (some sign) m K H := ⟨tail, childLegal⟩
        have ih := induction (some sign) m B left childLarge child good
        subst n
        let childHistory := history child left (by omega)
        let parentHistory := EndpointHistory.discard sign (show 0 < left by omega)
          (show 0 < size.val + 1 by omega) compatible shape childHistory
        have decoded : history ⟨.discard sign size shape tail, legal⟩
            (left + (size.val + 1)) (by omega) = parentHistory := by
          dsimp only [history, decode]
          apply eq_of_heq
          apply HEq.trans (eqRec_heq _ _)
          congr 2 <;> simp [history, childHistory, child]
        revert sample
        rw [decoded]
        intro sample
        let first : Indecomposable sign left :=
          ⟨childHistory.assemble sample, ((endpoint_history_count_kernel childHistory).1 sample).1⟩
        let π : Carrier state (left + (size.val + 1)) :=
          ⟨parentHistory.assemble sample, ((endpoint_history_count_kernel parentHistory).1 sample).1⟩
        change CappedExploration.classify m B (H + 1) K π = (parentHistory, .good)
        simp only [CappedExploration.classify, explore, Nat.recAux,
          dif_neg (show m ≠ 0 by omega), dif_neg (show ¬left + (size.val + 1) < 2 by omega)]
        have inv := inverse sign (show 0 < left by omega)
          (show 0 < size.val + 1 by omega) first shape π rfl
          ((endpoint_history_count_kernel parentHistory).1 sample).2.1
        generalize hr : recover π (by omega) = recovered at inv ⊢
        rcases recovered with ⟨s, a, b, ha, hb, eq, compat, recoveredFirst, last,
          reconstruction, mincut, unique, factorUnique⟩
        dsimp only at inv
        rcases inv with ⟨hs, haEq, hbEq, hfirst, hlast⟩
        subst s
        subst a
        subst b
        cases hfirst
        cases hlast
        have hsmall : ¬left + (size.val + 1) < 2 := by omega
        have hleft : ¬left ≤ K := by omega
        have hcap : size.val + 1 ≤ K := by omega
        have ichild := ih sample
        have ihistory := congrArg Prod.fst ichild
        have ikind := congrArg Prod.snd ichild
        change (explore (state := some sign) m B K H first).history = childHistory at ihistory
        change (explore (state := some sign) m B K H first).kind = .good at ikind
        simp only [dif_neg hleft, dif_pos hcap]
        change (EndpointHistory.discard sign _ _ compatible shape
          (explore (state := some sign) m B K H first).history,
          (explore (state := some sign) m B K H first).kind) = (parentHistory, .good)
        rw [ihistory, ikind]
  intro state m B n large code good π
  constructor
  · rintro ⟨allowed, equality⟩
    have historyEq := congrArg Prod.fst equality
    have event : (explore m B K H ⟨π, allowed⟩).history.Event π :=
      ⟨(explore m B K H ⟨π, allowed⟩).sample, (explore m B K H ⟨π, allowed⟩).reconstruct⟩
    change (explore m B K H ⟨π, allowed⟩).history = _ at historyEq
    rwa [historyEq] at event
  · rintro ⟨sample, rfl⟩
    exact ⟨((endpoint_history_count_kernel _).1 sample).1,
      roundtrip H state m B n large code good sample⟩

#print axioms stable_success_fibers

theorem stable_code_transport (K H : ℕ) :
    (∀ (state : Option Bool) (m n : ℕ) (large : H * K < n)
      (code : StableCode state m K H),
      let supplied := history code n large
      supplied.steps ≤ H ∧ supplied.Capped K ∧
      (∀ alphabet low, supplied.word alphabet low = word code.val alphabet low) ∧
      compress supplied (terminal code.val) K H = some code.val ∧
      (terminal code.val = .good → m ≤ supplied.emitted)) ∧
    (∀ (state : Option Bool) (m B n : ℕ)
      (large : H * K + max (2 * K) (max m B) < n) (π : Carrier state n),
      let code := boundedClassify m B K H large π
      CappedExploration.classify m B H K π =
        (history code n (by omega), terminal code.val)) := by
  classical
  have structural : ∀ (H : ℕ) (state : Option Bool) (m n : ℕ) (large : H * K < n)
      (code : StableCode state m K H),
      let supplied := history code n large
      supplied.steps ≤ H ∧ supplied.Capped K ∧
      (∀ alphabet low, supplied.word alphabet low = word code.val alphabet low) ∧
      compress supplied (terminal code.val) K H = some code.val ∧
      (terminal code.val = .good → m ≤ supplied.emitted) := by
    intro H
    induction H with
    | zero =>
      intro state m n large code
      rcases code with ⟨code, legal⟩
      cases code with
      | stop kind =>
        refine ⟨by simp [history, decode, EndpointHistory.steps], trivial,
          by simp [history, decode, EndpointHistory.word, word], rfl, ?_⟩
        intro good
        dsimp only [terminal] at good
        rw [good] at legal
        have hm : m = 0 := by simpa [Legal] using legal
        simp [hm]
    | succ H induction =>
      intro state m n large code
      rcases code with ⟨code, legal⟩
      cases code with
      | stop kind =>
        refine ⟨by simp [history, decode, EndpointHistory.steps], trivial,
          by simp [history, decode, EndpointHistory.word, word], rfl, ?_⟩
        intro good
        dsimp only [terminal] at good
        rw [good] at legal
        have hm : m = 0 := by simpa [Legal] using legal
        simp [hm]
      | emit sign size shape tail =>
        have bound := size.isLt
        have parent := large
        rw [Nat.succ_mul] at parent
        generalize rightEq : n - (size.val + 1) = right
        have nEq : n = size.val + 1 + right := by omega
        have childLarge : H * K < right := by omega
        let child : StableCode none (m - (size.val + 1)) K H := ⟨tail, legal.2.2⟩
        have ih := induction none (m - (size.val + 1)) right childLarge child
        subst n
        let childHistory := history child right childLarge
        let parentHistory := EndpointHistory.emit sign (show 0 < size.val + 1 by omega)
          (show 0 < right by omega) legal.2.1 shape childHistory
        change childHistory.steps ≤ H ∧ childHistory.Capped K ∧
          (∀ alphabet low, childHistory.word alphabet low = word tail alphabet low) ∧
          compress childHistory (terminal tail) K H = some tail ∧
          (terminal tail = .good → m - (size.val + 1) ≤ childHistory.emitted) at ih
        have decoded : history ⟨.emit sign size shape tail, legal⟩
            (size.val + 1 + right) large = parentHistory := by
          dsimp only [history, decode]
          apply eq_of_heq
          apply HEq.trans (eqRec_heq _ _)
          congr 2 <;> simp [history, childHistory, child]
        rw [decoded]
        refine ⟨by dsimp [parentHistory, EndpointHistory.steps]; omega,
          ⟨by omega, ih.2.1⟩, ?_, ?_, ?_⟩
        · intro alphabet low
          dsimp [parentHistory, EndpointHistory.word, word]
          rw [ih.2.2.1]
        · dsimp [parentHistory, compress]
          simp only [if_pos (show size.val + 1 ≤ K by omega),
            dif_pos (show size.val + 1 ≤ K by omega), Nat.add_sub_cancel,
            terminal, ih.2.2.2.1, Option.map_some]
        · intro good
          have emitted := ih.2.2.2.2 good
          dsimp [parentHistory, EndpointHistory.emitted]
          omega
      | discard sign size shape tail =>
        have bound := size.isLt
        have parent := large
        rw [Nat.succ_mul] at parent
        generalize leftEq : n - (size.val + 1) = left
        have nEq : n = left + (size.val + 1) := by omega
        have childLarge : H * K < left := by omega
        let child : StableCode (some sign) m K H := ⟨tail, legal.2.2⟩
        have ih := induction (some sign) m left childLarge child
        subst n
        let childHistory := history child left childLarge
        let parentHistory := EndpointHistory.discard sign (show 0 < left by omega)
          (show 0 < size.val + 1 by omega) legal.2.1 shape childHistory
        change childHistory.steps ≤ H ∧ childHistory.Capped K ∧
          (∀ alphabet low, childHistory.word alphabet low = word tail alphabet low) ∧
          compress childHistory (terminal tail) K H = some tail ∧
          (terminal tail = .good → m ≤ childHistory.emitted) at ih
        have decoded : history ⟨.discard sign size shape tail, legal⟩
            (left + (size.val + 1)) large = parentHistory := by
          dsimp only [history, decode]
          apply eq_of_heq
          apply HEq.trans (eqRec_heq _ _)
          congr 2 <;> simp [history, childHistory, child]
        rw [decoded]
        refine ⟨by dsimp [parentHistory, EndpointHistory.steps]; omega,
          ⟨by omega, ih.2.1⟩, ?_, ?_, ?_⟩
        · intro alphabet low
          dsimp [parentHistory, EndpointHistory.word, word]
          exact ih.2.2.1 _ _
        · dsimp [parentHistory, compress]
          simp only [if_pos (show size.val + 1 ≤ K by omega),
            dif_pos (show size.val + 1 ≤ K by omega), Nat.add_sub_cancel,
            terminal, ih.2.2.2.1, Option.map_some]
        · exact ih.2.2.2.2
  refine ⟨structural H, ?_⟩
  have actual : ∀ (H : ℕ) (state : Option Bool) (m B n : ℕ)
      (large : H * K + max (2 * K) (max m B) < n) (π : Carrier state n),
      let code := boundedClassify m B K H large π
      CappedExploration.classify m B H K π =
        (history code n (by omega), terminal code.val) := by
    intro H
    induction H with
    | zero =>
      intro state m B n large π
      have hb : B < n := by omega
      by_cases hm : m = 0
      · simp [CappedExploration.classify, explore, boundedClassify, history, decode,
          terminal, Nat.recAux, hm, hb]
      · have hn : ¬n < 2 := by
          have : m ≤ max (2 * K) (max m B) := le_trans (le_max_left _ _) (le_max_right _ _)
          omega
        simp [CappedExploration.classify, explore, boundedClassify, history, decode,
          terminal, Nat.recAux, hm, hb, hn]
        omega
    | succ H induction =>
      intro state m B n large π
      have sameSize {root} (code : Code K H) (valid : Compatible root code)
          (first last : ℕ) (hf : H * K < first) (hl : H * K < last) (eq : first = last) :
          HEq (decode code valid first hf) (decode code valid last hl) := by
        cases eq
        rfl
      by_cases hm : m = 0
      · have hb : B < n := by omega
        simp [CappedExploration.classify, explore, boundedClassify, history, decode,
          terminal, Nat.recAux, hm, hb]
      have hn : ¬n < 2 := by
        have : m ≤ max (2 * K) (max m B) := le_trans (le_max_left _ _) (le_max_right _ _)
        omega
      simp only [CappedExploration.classify, explore, Nat.recAux, dif_neg hm, dif_neg hn]
      generalize hrec : recover π (by omega) = recovered
      rcases recovered with ⟨sign, left, right, hl, hr, equality, compatible, first, last,
        reconstruction, mincut, unique, factorUnique⟩
      subst n
      simp only [boundedClassify, dif_neg hm]
      rw [hrec]
      simp only [codeStep]
      have parent := large
      rw [Nat.succ_mul] at parent
      by_cases hleft : left ≤ K
      · have childLarge : H * K + max (2 * K) (max (m - left) B) < right := by
          have smaller : max (2 * K) (max (m - left) B) ≤ max (2 * K) (max m B) :=
            max_le_max_left _ (max_le_max_right _ (Nat.sub_le _ _))
          omega
        have ih := induction none (m - left) B right childLarge ⟨last, trivial⟩
        simp only [dif_pos hleft]
        dsimp only [history, decode]
        apply Prod.ext
        · apply eq_of_heq
          apply HEq.trans _ (eqRec_heq _ _).symm
          have firstEq := congrArg Prod.fst ih
          change (explore (state := none) (m - left) B K H ⟨last, trivial⟩).history = _ at firstEq
          change HEq (EndpointHistory.emit sign hl hr compatible first
            (explore (state := none) (m - left) B K H ⟨last, trivial⟩).history) _
          rw [firstEq]
          congr 3 <;> simp [Nat.sub_add_cancel (show 1 ≤ left by omega)]
          all_goals
            dsimp only [history]
            apply sameSize
            omega
        · change (explore (state := none) (m - left) B K H ⟨last, trivial⟩).kind = _
          exact congrArg Prod.snd ih
      · by_cases hright : right ≤ K
        · have childLarge : H * K + max (2 * K) (max m B) < left := by omega
          have ih := induction (some sign) m B left childLarge first
          simp only [dif_neg hleft, dif_pos hright]
          dsimp only [history, decode]
          apply Prod.ext
          · apply eq_of_heq
            apply HEq.trans _ (eqRec_heq _ _).symm
            have firstEq := congrArg Prod.fst ih
            change (explore (state := some sign) m B K H first).history = _ at firstEq
            change HEq (EndpointHistory.discard sign hl hr compatible last
              (explore (state := some sign) m B K H first).history) _
            rw [firstEq]
            congr 3 <;> simp [Nat.sub_add_cancel (show 1 ≤ right by omega)]
            all_goals
              dsimp only [history]
              apply sameSize
              omega
          · change (explore (state := some sign) m B K H first).kind = _
            exact congrArg Prod.snd ih
        · simp [dif_neg hleft, dif_neg hright, history, decode, terminal]
  exact actual H

#print axioms stable_code_transport

def codeFiber {state m B n K H}
    (large : H * K + max (2 * K) (max m B) < n) (code : StableCode state m K H) :
    Avoider n → Prop := Fiber m B H K (history code n (by omega), terminal code.val)

open Classical in
noncomputable def cylinderMass {state m B n K H}
    (large : H * K + max (2 * K) (max m B) < n)
    (test : List (Option (Fin B)) → Prop) (code : StableCode state m K H) : ℝ :=
  if terminal code.val = .good then
    if test ((word code.val B 0).take m) then
      actualMass n (Allowed state) * (history code n (by omega)).weight else 0
  else actualMass n (fun π => codeFiber large code π ∧
    test ((EndpointHistory.literal π B 0).take m))

open Classical in
noncomputable def noFixedMass {state m B n K H}
    (large : H * K + max (2 * K) (max m B) < n) (code : StableCode state m K H) : ℝ :=
  if terminal code.val = .good then
    if EndpointHistory.NoFixedWord m ((word code.val m 0).take m) then
      actualMass n (Allowed state) * (history code n (by omega)).weight else 0
  else actualMass n (fun π => codeFiber large code π ∧ EndpointHistory.AbsoluteNoFixed m π)

open Classical in
theorem stable_finite_mass_sums (state : Option Bool) (m B K H n : ℕ)
    (large : H * K + max (2 * K) (max m B) < n) :
    (∀ π : Avoider n, Allowed state π ↔
      ∃! code : StableCode state m K H, codeFiber large code π) ∧
    (∀ code : StableCode state m K H,
      let outcome := (history code n (by omega), terminal code.val)
      Nat.card {π : Avoider n // codeFiber large code π} =
        Nat.card {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} ∧
      actualMass n (codeFiber large code) / actualMass n (Allowed state) =
        outcome.1.weight *
          (Nat.card {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} : ℝ) /
            Nat.card outcome.1.Leaf ∧
      (terminal code.val = .good →
        actualMass n (codeFiber large code) / actualMass n (Allowed state) = outcome.1.weight)) ∧
    (∀ event : Avoider n → Prop,
      Nat.card {π : Avoider n // Allowed state π ∧ event π} =
        ∑ code : StableCode state m K H,
          Nat.card {π : Avoider n // codeFiber large code π ∧ event π} ∧
      actualMass n (fun π => Allowed state π ∧ event π) =
        ∑ code : StableCode state m K H,
          actualMass n (fun π => codeFiber large code π ∧ event π)) ∧
    (∀ test : List (Option (Fin B)) → Prop,
      actualMass n (fun π => Allowed state π ∧
        test ((EndpointHistory.literal π B 0).take m)) =
      ∑ code : StableCode state m K H, cylinderMass large test code) ∧
    (actualMass n (fun π => Allowed state π ∧ EndpointHistory.AbsoluteNoFixed m π) =
      ∑ code : StableCode state m K H, noFixedMass large code) := by
  classical
  have mass (event : Avoider n → Prop) : actualMass n event =
      (Nat.card {π : Avoider n // event π} : ℝ) / Nat.card (Avoider n) := by
    let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
    change ((PMF.uniformOfFintype (Avoider n)).toOuterMeasure {π | event π}).toReal = _
    rw [PMF.toOuterMeasure_uniformOfFintype_apply]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.card_eq_fintype_card]
    rfl
  have sourcePositive : actualMass n (Allowed state) ≠ 0 := by
    let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
    let : Nonempty (Carrier state n) := ⟨carrierWitness _ _⟩
    rw [mass]
    apply div_ne_zero
    · exact_mod_cast (Nat.card_pos (α := Carrier state n)).ne'
    · exact_mod_cast (Nat.card_pos (α := Avoider n)).ne'
  have injective : Function.Injective
      (fun code : StableCode state m K H =>
        (history code n (by omega), terminal code.val)) := by
    intro first last equality
    have firstLaw := ((stable_code_transport K H).1 state m n (by omega) first).2.2.2.1
    have lastLaw := ((stable_code_transport K H).1 state m n (by omega) last).2.2.2.1
    have codes := congrArg (fun outcome : Outcome state n => compress outcome.1 outcome.2 K H) equality
    rw [firstLaw, lastLaw] at codes
    exact Subtype.ext (Option.some.inj codes)
  have partition (π : Avoider n) : Allowed state π ↔
      ∃! code : StableCode state m K H, codeFiber large code π := by
    constructor
    · intro allowed
      let code := boundedClassify m B K H large ⟨π, allowed⟩
      have law := (stable_code_transport K H).2 state m B n large ⟨π, allowed⟩
      refine ⟨code, ⟨allowed, law⟩, ?_⟩
      rintro other ⟨otherAllowed, otherLaw⟩
      apply injective
      exact otherLaw.symm.trans law
    · rintro ⟨_, ⟨allowed, _⟩, _⟩
      exact allowed
  have counts (event : Avoider n → Prop) :
      Nat.card {π : Avoider n // Allowed state π ∧ event π} =
        ∑ code : StableCode state m K H,
          Nat.card {π : Avoider n // codeFiber large code π ∧ event π} := by
    let total := Σ code : StableCode state m K H,
      {π : Avoider n // codeFiber large code π ∧ event π}
    let mapping : total → {π : Avoider n // Allowed state π ∧ event π} :=
      fun item => ⟨item.2.val, item.2.property.1.choose, item.2.property.2⟩
    have oneToOne : Function.Injective mapping := by
      rintro ⟨first, firstπ⟩ ⟨last, lastπ⟩ equality
      have actualEq : firstπ.val = lastπ.val := congrArg Subtype.val equality
      have codeEq : first = last := by
        obtain ⟨chosen, _, unique⟩ := (partition firstπ.val).mp firstπ.property.1.choose
        have other := lastπ.property.1
        rw [← actualEq] at other
        exact (unique first firstπ.property.1).trans (unique last other).symm
      subst last
      have actual : firstπ = lastπ := Subtype.ext actualEq
      cases actual
      rfl
    have onto : Function.Surjective mapping := by
      rintro ⟨π, allowed, tested⟩
      obtain ⟨code, fiber, _⟩ := (partition π).mp allowed
      exact ⟨⟨code, ⟨π, fiber, tested⟩⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective mapping ⟨oneToOne, onto⟩)]
    simp only [total, Nat.card_eq_fintype_card, Fintype.card_sigma]
  have massSum (event : Avoider n → Prop) :
      actualMass n (fun π => Allowed state π ∧ event π) =
        ∑ code : StableCode state m K H,
          actualMass n (fun π => codeFiber large code π ∧ event π) := by
    simp only [mass, counts, Nat.cast_sum, Finset.sum_div]
  have goodEvent (code : StableCode state m K H) (good : terminal code.val = .good) :
      codeFiber large code = (history code n (by omega)).Event := by
    funext π
    apply propext
    simpa only [codeFiber, good] using stable_success_fibers K H state m B n large code good π
  have goodMass (code : StableCode state m K H) (good : terminal code.val = .good) :
      actualMass n (codeFiber large code) =
        actualMass n (Allowed state) * (history code n (by omega)).weight := by
    rw [goodEvent code good]
    have law := (endpoint_history_count_kernel (history code n (by omega))).2.2.2.1
    exact (div_eq_iff sourcePositive).mp law |>.trans (mul_comm _ _)
  have goodBounds (code : StableCode state m K H) (good : terminal code.val = .good) :
      m ≤ (history code n (by omega)).emitted ∧
        max (2 * K) (max m B) < (history code n (by omega)).remaining := by
    have structuralLaw := (stable_code_transport K H).1 state m n (by omega) code
    have removed := ((endpoint_history_count_kernel (history code n (by omega))).2.2.2.2.2.2.1
      K structuralLaw.2.1).trans (Nat.mul_le_mul_right K structuralLaw.1)
    have sizeEq := (endpoint_history_count_kernel (history code n (by omega))).2.2.2.2.2.1
    exact ⟨structuralLaw.2.2.2.2 good, by omega⟩
  refine ⟨partition, ?_, fun event => ⟨counts event, massSum event⟩, ?_, ?_⟩
  · intro code
    have restricted := (actual_capped_partition state n m B H K).2.2.1
      (history code n (by omega), terminal code.val)
    refine ⟨restricted.1, restricted.2.2.2, ?_⟩
    intro good
    rw [goodEvent code good]
    exact (endpoint_history_count_kernel (history code n (by omega))).2.2.2.1
  · intro test
    rw [massSum]
    apply Finset.sum_congr rfl
    intro code member
    unfold cylinderMass
    by_cases good : terminal code.val = .good
    · rw [if_pos good, goodEvent code good]
      have bounds := goodBounds code good
      have law := (endpoint_history_literal_cylinder (history code n (by omega))).2.1
        B m (by omega) bounds.1 test
      rw [law, ((stable_code_transport K H).1 state m n (by omega) code).2.2.1]
      rw [← goodEvent code good, goodMass code good]
    · rw [if_neg good]
  · rw [massSum]
    apply Finset.sum_congr rfl
    intro code member
    unfold noFixedMass
    by_cases good : terminal code.val = .good
    · rw [if_pos good, goodEvent code good]
      have bounds := goodBounds code good
      have law := (endpoint_history_literal_cylinder (history code n (by omega))).2.2.2
        m (by omega) bounds.1
      rw [law, ((stable_code_transport K H).1 state m n (by omega) code).2.2.1]
      rw [← goodEvent code good, goodMass code good]
    · rw [if_neg good]

#print axioms stable_finite_mass_sums

end D5.S1.Words.Patterns.Separable.StableEndpointCodes
