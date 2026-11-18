/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.markedPartitionEquiv; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinMarkedPath.contractEquiv
   digest: Reversible deletion of the previous pair in the literal eight-colour path. -/

/-
admission_basis: escape-witness
escape_witness: contract/expand reconstruct each actual path word at every length;
used-pair admissibility is preserved in both directions. The existing partition
inverse supplies the unlabelled objects, rather than a separately chosen count.
contractEquiv: proof_shape=content; consumers=pathEquiv, sixContractEquiv
pathEquiv: proof_shape=content; consumers=markedPartitionEquiv, sixContractEquiv
evenMarkEquiv: proof_shape=content; consumer=signMarkEquiv
markedPartitionEquiv: proof_shape=content; reversible source four-pair application
sixLiteralEquiv: proof_shape=bind-only; consumer=sixMarkedPartitionEquiv
sixContractEquiv: proof_shape=content; consumer=sixMarkedPartitionEquiv
sixMarkedPartitionEquiv: proof_shape=content; actual at-most-two-block application
All private helpers lie on these live inverse and source-reconstruction paths.
The new public mathematical constructions are equivalence definitions, with
both inverse proofs in their terms. Exact terminal cardinal, series and matrix
applications are transient and are not new retained theorem wrappers.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import Mathlib.Logic.Equiv.Bool

/-! Britnell--Wildon Proposition 8.1: delete the previous pair label, retaining
all noninitial signs. The existing graph partition inverse supplies the
unlabelled blocks; their minima carry the forced signs. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinMarkedPath
open HardinGraphNormalization
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

/-- Complementary pairs 0/7, 1/6, 2/5, 3/4. -/
def beta8 (c : Fin 8) : Fin 4 := ⟨min c.val (7-c.val), by omega⟩
private def lift8 (p : Fin 4) (b : Bool) : Fin 8 :=
  if b then ⟨7-p.val, by omega⟩ else ⟨p.val, by omega⟩
private def lower (p : Fin 4) (c : Fin 8) : Fin 6 :=
  HardinGraphNormalization.lift
    ⟨if (beta8 c).val < p.val then (beta8 c).val else (beta8 c).val-1, by
      have := (beta8 c).isLt; have := p.isLt; split <;> omega⟩ (decide (4 ≤ c.val))
private def raise (p : Fin 4) (c : Fin 6) : Fin 8 :=
  lift8 ⟨if (beta c).val < p.val then (beta c).val else (beta c).val+1, by
    have := (beta c).isLt; split <;> omega⟩ (decide (3 ≤ c.val))

/-- The number of used source pairs minus one. -/
private def next8 (u : Fin 4) (c : Fin 8) : Fin 4 :=
  ⟨max u.val (beta8 c).val, max_lt u.isLt (beta8 c).isLt⟩
private def next6 (u : Fin 4) (c : Fin 6) : Fin 4 :=
  ⟨max u.val ((beta c).val+1), by have := (beta c).isLt; have := u.isLt; omega⟩
private def allow8 (u : Fin 4) (c : Fin 8) : Prop :=
  (beta8 c).val ≤ u.val ∨ c.val = u.val+1
private def allow6 (u : Fin 4) (c : Fin 6) : Prop :=
  (beta c).val < u.val ∨ c.val = u.val
private instance (u : Fin 4) (c : Fin 8) : Decidable (allow8 u c) :=
  inferInstanceAs (Decidable (_ ∨ _))
private instance (u : Fin 4) (c : Fin 6) : Decidable (allow6 u c) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem step_certificate :
    (∀ p c, lower p (raise p c) = c) ∧
    (∀ p c, beta8 c ≠ p → raise p (lower p c) = c) ∧
    (∀ p c, beta8 (raise p c) ≠ p) ∧
    (∀ u p c, p.val ≤ u.val → beta8 c ≠ p →
      (allow8 u c ↔ allow6 u (lower p c)) ∧ next8 u c = next6 u (lower p c)) ∧
    (∀ u p c, p.val ≤ u.val →
      (allow6 u c ↔ allow8 u (raise p c)) ∧ next6 u c = next8 u (raise p c)) := by
  decide +kernel

private def sourceGood : {n : ℕ} → Fin 4 → Fin 4 → (Fin n → Fin 8) → Prop
  | 0, _, _, _ => True
  | _+1, u, p, f => allow8 u (f 0) ∧ beta8 (f 0) ≠ p ∧
      sourceGood (next8 u (f 0)) (beta8 (f 0)) (Fin.tail f)
private def targetGood : {n : ℕ} → Fin 4 → (Fin n → Fin 6) → Prop
  | 0, _, _ => True
  | _+1, u, f => allow6 u (f 0) ∧ targetGood (next6 u (f 0)) (Fin.tail f)

private def contract : {n : ℕ} → Fin 4 → (Fin n → Fin 8) → (Fin n → Fin 6)
  | 0, _, _ => Fin.elim0
  | _+1, p, f => Fin.cons (lower p (f 0)) (contract (beta8 (f 0)) (Fin.tail f))
private def expand : {n : ℕ} → Fin 4 → (Fin n → Fin 6) → (Fin n → Fin 8)
  | 0, _, _ => Fin.elim0
  | _+1, p, f => Fin.cons (raise p (f 0)) (expand (beta8 (raise p (f 0))) (Fin.tail f))

private theorem contract_expand {n : ℕ} (p : Fin 4) (f : Fin n → Fin 6) :
    contract p (expand p f) = f := by
  induction n generalizing p with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [contract, expand, Fin.cons_zero, Fin.tail_cons, step_certificate.1]
    rw [ih]
    exact Fin.cons_self_tail _

private theorem expand_contract {n : ℕ} (u p : Fin 4) (f : Fin n → Fin 8)
    (h : sourceGood u p f) : expand p (contract p f) = f := by
  induction n generalizing u p with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rcases h with ⟨ha,hp,ht⟩
    have he := step_certificate.2.1 p (f 0) hp
    simp only [contract, expand, Fin.cons_zero, Fin.tail_cons, he]
    rw [ih _ _ _ ht]
    exact Fin.cons_self_tail _

private theorem contract_good {n : ℕ} (u p : Fin 4) (f : Fin n → Fin 8)
    (hp : p.val ≤ u.val) (h : sourceGood u p f) : targetGood u (contract p f) := by
  induction n generalizing u p with
  | zero => trivial
  | succ n ih =>
    rcases h with ⟨ha,hne,ht⟩
    obtain ⟨he,hn⟩ := step_certificate.2.2.2.1 u p (f 0) hp hne
    refine ⟨he.mp ha, ?_⟩
    change targetGood (next6 u (lower p (f 0))) (contract (beta8 (f 0)) (Fin.tail f))
    rw [← hn]
    exact ih _ _ _ (Nat.le_max_right _ _) ht

private theorem expand_good {n : ℕ} (u p : Fin 4) (f : Fin n → Fin 6)
    (hp : p.val ≤ u.val) (h : targetGood u f) : sourceGood u p (expand p f) := by
  induction n generalizing u p with
  | zero => trivial
  | succ n ih =>
    rcases h with ⟨ha,ht⟩
    obtain ⟨he,hn⟩ := step_certificate.2.2.2.2 u p (f 0) hp
    refine ⟨he.mp ha, step_certificate.2.2.1 _ _, ?_⟩
    change sourceGood (next8 u (raise p (f 0))) (beta8 (raise p (f 0)))
      (expand (beta8 (raise p (f 0))) (Fin.tail f))
    rw [← hn]
    apply ih _ _ _ _ ht
    rw [hn]
    exact Nat.le_max_right _ _

/-- The actual three predecessor flags, with no pair removed from the source palette. -/
abbrev Seen8 := Bool × Bool × Bool
private def allowed8 (s : Seen8) (c : Fin 8) : Prop :=
  ((c=2 ∨ c=3 ∨ c=4 ∨ c=5 ∨ c=6) → s.1 = true) ∧
  ((c=3 ∨ c=4 ∨ c=5) → s.2.1 = true) ∧ (c=4 → s.2.2 = true)
private instance (s : Seen8) (c : Fin 8) : Decidable (allowed8 s c) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _) ∧ (_ → _)))
private def advance8 (s : Seen8) (c : Fin 8) : Seen8 :=
  (s.1 || decide (c=1), s.2.1 || decide (c=2), s.2.2 || decide (c=3))
def good8 : {n : ℕ} → Seen8 → (Fin n → Fin 8) → Prop
  | 0, _, _ => True
  | _+1, s, f => allowed8 s (f 0) ∧ good8 (advance8 s (f 0)) (Fin.tail f)
private def flags8 (u : Fin 4) : Seen8 :=
  (decide (1 ≤ u.val), decide (2 ≤ u.val), decide (3 ≤ u.val))
private def flags6 (u : Fin 4) : HardinA233175PairStrip.Seen :=
  (decide (2 ≤ u.val), decide (3 ≤ u.val))
private def chain8 : {n : ℕ} → Fin 4 → (Fin n → Fin 8) → Prop
  | 0, _, _ => True
  | _+1, p, f => beta8 (f 0) ≠ p ∧ chain8 (beta8 (f 0)) (Fin.tail f)

private theorem scanner_certificate :
    (∀ u c, allowed8 (flags8 u) c ↔ allow8 u c) ∧
    (∀ u c, allow8 u c → advance8 (flags8 u) c = flags8 (next8 u c)) ∧
    (∀ u c, 0 < u.val → (HardinA233175PairStrip.allowed (flags6 u) c ↔ allow6 u c)) ∧
    (∀ u c, allow6 u c → HardinA233175PairStrip.advance (flags6 u) c = flags6 (next6 u c)) ∧
    (∀ c, allow6 0 c ↔ c=0) := by
  decide +kernel

private theorem source_good_iff {n : ℕ} (u p : Fin 4) (f : Fin n → Fin 8) :
    sourceGood u p f ↔ good8 (flags8 u) f ∧ chain8 p f := by
  induction n generalizing u p with
  | zero => simp [sourceGood,good8,chain8]
  | succ n ih =>
    simp only [sourceGood,good8,chain8,scanner_certificate.1,ih]
    constructor
    · rintro ⟨ha,hn,hg,hc⟩
      exact ⟨⟨ha, by rwa [scanner_certificate.2.1 u _ ha]⟩,hn,hc⟩
    · rintro ⟨⟨ha,hg⟩,hn,hc⟩
      exact ⟨ha,hn,by rwa [scanner_certificate.2.1 u _ ha] at hg,hc⟩

private theorem target_good_iff {n : ℕ} (u : Fin 4) (f : Fin n → Fin 6) (hu : 0 < u.val) :
    targetGood u f ↔ HardinA233175PairStrip.good (flags6 u) f := by
  induction n generalizing u with
  | zero => simp [targetGood,HardinA233175PairStrip.good]
  | succ n ih =>
    simp only [targetGood,HardinA233175PairStrip.good,scanner_certificate.2.2.1 u _ hu]
    constructor
    · rintro ⟨ha,ht⟩
      rw [scanner_certificate.2.2.2.1 u _ ha]
      exact ⟨ha,(ih _ _ (lt_of_lt_of_le hu (Nat.le_max_left _ _))).mp ht⟩
    · rintro ⟨ha,ht⟩
      rw [scanner_certificate.2.2.2.1 u _ ha] at ht
      exact ⟨ha,(ih _ _ (lt_of_lt_of_le hu (Nat.le_max_left _ _))).mpr ht⟩

/-- The source predecessor clauses are literal, including absent-colour vacuity. -/
private theorem good8_iff {n : ℕ} (s : Seen8) (f : Fin n → Fin 8) :
    good8 s f ↔ ∀ i,
      ((f i = 2 ∨ f i = 3 ∨ f i = 4 ∨ f i = 5 ∨ f i = 6) → s.1 = true ∨ ∃ j, j < i ∧ f j = 1) ∧
      ((f i = 3 ∨ f i = 4 ∨ f i = 5) → s.2.1 = true ∨ ∃ j, j < i ∧ f j = 2) ∧
      (f i = 4 → s.2.2 = true ∨ ∃ j, j < i ∧ f j = 3) := by
  induction n generalizing s with
  | zero => simp [good8]
  | succ n ih =>
    simp only [good8,ih,Fin.forall_fin_succ]
    have hp : ∀ i : Fin n, (0 : Fin (n+1)) < i.succ := fun _ => Nat.zero_lt_succ _
    simp [Fin.tail,Fin.exists_fin_succ,advance8,allowed8,or_assoc,hp]

/-- Independent definition of the literal eight-colour path. -/
def Path8 (n : ℕ) := {f : Fin (n+1) → Fin 8 // f 0=0 ∧
  (∀ i,
    ((f i = 2 ∨ f i = 3 ∨ f i = 4 ∨ f i = 5 ∨ f i = 6) → ∃ j, j < i ∧ f j = 1) ∧
    ((f i = 3 ∨ f i = 4 ∨ f i = 5) → ∃ j, j < i ∧ f j = 2) ∧
    (f i = 4 → ∃ j, j < i ∧ f j = 3)) ∧ ∀ i : Fin n,
    f i.castSucc ≠ f i.succ ∧ (f i.castSucc).val+(f i.succ).val ≠ 7}

private theorem chain8_local {n : ℕ} (f : Fin (n+1) → Fin 8) :
    chain8 (beta8 (f 0)) (Fin.tail f) ↔ ∀ i : Fin n,
      f i.castSucc ≠ f i.succ ∧ (f i.castSucc).val+(f i.succ).val ≠ 7 := by
  have bond : ∀ a b : Fin 8, beta8 a ≠ beta8 b ↔ a≠b ∧ a.val+b.val≠7 := by decide +kernel
  induction n with
  | zero => simp [chain8]
  | succ n ih =>
    have ht := ih (Fin.tail f)
    simp only [chain8,Fin.forall_fin_succ,Fin.tail] at ht ⊢
    rw [← bond]
    simpa [ne_comm] using (and_congr Iff.rfl ht)

private noncomputable def sourceEquiv (n : ℕ) :
    Path8 n ≃ {f : Fin n → Fin 8 // sourceGood 0 0 f} where
  toFun f := ⟨Fin.tail f.val, (source_good_iff _ _ _).mpr ⟨by
    have h : good8 (false,false,false) f.val :=
      (good8_iff _ _).mpr (by simpa using f.property.2.1)
    simpa [good8,f.property.1,advance8,flags8] using h.2,
    by simpa [f.property.1,beta8] using (chain8_local f.val).mpr f.property.2.2⟩⟩
  invFun f := ⟨Fin.cons 0 f.val,rfl,by
    have h := (source_good_iff _ _ _).mp f.property
    refine ⟨?_,(chain8_local _).mp ?_⟩
    · have hg : good8 (false,false,false) (Fin.cons 0 f.val) := by
        simpa [good8,allowed8,advance8,flags8] using h.1
      simpa using (good8_iff _ _).mp hg
    · simpa [beta8] using h.2⟩
  left_inv f := Subtype.ext (by simpa [f.property.1] using Fin.cons_self_tail f.val)
  right_inv f := Subtype.ext (by funext i; rfl)

private noncomputable def targetEquiv (n : ℕ) :
    {f : Fin (n+1) → Fin 6 // targetGood 0 f} ≃ Legal (⊥ : SimpleGraph (Fin (n+1))) where
  toFun f := ⟨f.val,by
    have h0 := scanner_certificate.2.2.2.2 (f.val 0) |>.mp f.property.1
    refine ⟨⟨h0,?_⟩,by simp⟩
    have ht := f.property.2
    simpa [HardinA233175PairStrip.good,h0,HardinA233175PairStrip.allowed,
      HardinA233175PairStrip.advance,next6,beta,flags6] using
      (target_good_iff 1 (Fin.tail f.val) (by decide)).mp (by simpa [h0,next6,beta] using ht)⟩
  invFun f := ⟨f.val,by
    have h0 := f.property.1.1
    refine ⟨(scanner_certificate.2.2.2.2 _).mpr h0,?_⟩
    have ht := f.property.1.2.2
    simpa [h0,next6,beta] using
      (target_good_iff 1 (Fin.tail f.val) (by decide)).mpr
        (by simpa [flags6,HardinA233175PairStrip.advance,h0] using ht)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The all-length word inverse; no enumerated-length restriction occurs. -/
noncomputable def contractEquiv (n : ℕ) :
    {f : Fin n → Fin 8 // sourceGood 0 0 f} ≃ {f : Fin n → Fin 6 // targetGood 0 f} where
  toFun f := ⟨contract 0 f.val,contract_good _ _ _ (by decide) f.property⟩
  invFun f := ⟨expand 0 f.val,expand_good _ _ _ (by decide) f.property⟩
  left_inv f := Subtype.ext (expand_contract _ _ _ f.property)
  right_inv f := Subtype.ext (contract_expand _ _)

/-- The source path is equivalent to the actual six-colour independent vertices. -/
noncomputable def pathEquiv (n : ℕ) : Path8 (n+1) ≃ Legal (⊥ : SimpleGraph (Fin (n+1))) :=
  (sourceEquiv (n+1)).trans ((contractEquiv (n+1)).trans (targetEquiv n))

/-- Actual even marks on each nonempty block: its minimum bit plus the
marked nonminimal vertices has even cardinality. -/
def EvenMarking {n : ℕ} (p : Fin n → Fin 3) :=
  {m : Fin n → Bool // ∀ i, First p i →
    ((if m i then 1 else 0) +
      ∑ j : Free p, if p j.val = p i ∧ m j.val = true then 1 else 0) % 2 = 0}

private theorem parity_bit (b : Bool) (k : ℕ) :
    ((if b then 1 else 0)+k) % 2 = 0 ↔ b = decide (k % 2 = 1) := by
  have h := Nat.mod_lt k (by decide : 0 < 2)
  cases b <;> simp <;> omega

private noncomputable def fillMarks {n : ℕ} (p : Fin n → Fin 3) (b : Free p → Bool)
    (i : Fin n) : Bool :=
  if h : First p i then
    decide ((∑ j : Free p, if p j.val = p i ∧ b j = true then 1 else 0) % 2 = 1)
  else b ⟨i,h⟩

/-- Filling the minimum by parity and forgetting it are inverse maps. -/
noncomputable def evenMarkEquiv {n : ℕ} (p : Fin n → Fin 3) :
    (Free p → Bool) ≃ EvenMarking p where
  toFun b := ⟨fillMarks p b, by
    intro i hi
    rw [parity_bit]
    simp only [fillMarks,dite_eq_left hi]
    congr 1
    congr 1
    apply congrArg (fun k : ℕ => k % 2)
    apply Finset.sum_congr rfl
    intro j _
    simp [j.property]⟩
  invFun m j := m.val j.val
  left_inv b := by funext j; simp [fillMarks,j.property]
  right_inv m := by
    apply Subtype.ext
    funext i
    by_cases hi : First p i
    · have h := (parity_bit (m.val i) _).mp (m.property i hi)
      simpa [fillMarks,hi] using h.symm
    · simp [fillMarks,hi]

private noncomputable def signMarkEquiv {n : ℕ} (p : Fin n → Fin 3) :
    (Free p → Bool) ≃ EvenMarking p :=
  (Equiv.piCongrRight fun _ => Equiv.boolNot).trans (evenMarkEquiv p)

/-- Proper unlabelled partitions into at most three blocks, each with an
actual even subset of marked elements; both inverse maps hold at every length. -/
noncomputable def markedPartitionEquiv (n : ℕ) : Path8 (n+1) ≃
    Σ S : StablePartition (⊥ : SimpleGraph (Fin (n+1))),
      EvenMarking (((partitionEquiv (⊥ : SimpleGraph (Fin (n+1)))).symm S).val) :=
  (pathEquiv n).trans ((literalPartitionEquiv _).trans
    (Equiv.sigmaCongrRight fun _S => signMarkEquiv _))


private theorem bound_certificate :
    (∀ (p : Fin 4) (c : Fin 8), p.val ≤ 2 → beta8 c ≠ p →
      ((beta8 c).val ≤ 2 ↔ (beta (lower p c)).val < 2)) ∧
    (∀ (p : Fin 4) (c : Fin 6), p.val ≤ 2 →
      ((beta (c)).val < 2 ↔ (beta8 (raise p c)).val ≤ 2)) := by decide +kernel

private theorem contract_bound {n : ℕ} (u p : Fin 4) (f : Fin n → Fin 8)
    (hp : p.val ≤ 2) (h : sourceGood u p f) :
    (∀ i, (beta8 (f i)).val ≤ 2) ↔ ∀ i, (beta (contract p f i)).val < 2 := by
  induction n generalizing u p with
  | zero => simp
  | succ n ih =>
    rcases h with ⟨ha,hne,ht⟩
    simp only [Fin.forall_fin_succ,contract,Fin.cons_zero,Fin.cons_succ]
    rw [← bound_certificate.1 p (f 0) hp hne]
    constructor
    · rintro ⟨h0,hh⟩
      exact ⟨h0,(ih _ _ _ h0 ht).mp hh⟩
    · rintro ⟨h0,hh⟩
      exact ⟨h0,(ih _ _ _ h0 ht).mpr hh⟩

private def emb6 (c : Fin 6) : Fin 8 :=
  lift8 ⟨(beta c).val, by have := (beta c).isLt; omega⟩ (decide (3 ≤ c.val))
private def unemb6 (c : Fin 8) : Fin 6 :=
  HardinGraphNormalization.lift ⟨min (beta8 c).val 2, by omega⟩ (decide (4 ≤ c.val))

private theorem embedding_certificate :
    (∀ c, unemb6 (emb6 c) = c) ∧
    (∀ c, (beta8 c).val ≤ 2 → emb6 (unemb6 c) = c) ∧
    (∀ c, (beta8 (emb6 c)).val ≤ 2) ∧
    (∀ s c, HardinA233175PairStrip.allowed s c ↔ allowed8 (s.1,s.2,false) (emb6 c)) ∧
    (∀ s c, advance8 (s.1,s.2,false) (emb6 c) =
      ((HardinA233175PairStrip.advance s c).1,(HardinA233175PairStrip.advance s c).2,false)) ∧
    (∀ c d, (c≠d ∧ c.val+d.val≠5) ↔
      (emb6 c≠emb6 d ∧ (emb6 c).val+(emb6 d).val≠7)) ∧
    (∀ c, emb6 c=0 ↔ c=0) := by decide +kernel

private theorem good_embedding {n : ℕ} (s : HardinA233175PairStrip.Seen)
    (f : Fin n → Fin 6) :
    HardinA233175PairStrip.good s f ↔ good8 (s.1,s.2,false) (emb6 ∘ f) := by
  induction n generalizing s with
  | zero => simp [HardinA233175PairStrip.good,good8]
  | succ n ih =>
    simp only [HardinA233175PairStrip.good,good8,Function.comp_apply,
      embedding_certificate.2.2.2.1,embedding_certificate.2.2.2.2.1,ih]
    rfl

/-- The literal three-pair source path, with the original complement five. -/
def Path6 (n : ℕ) := {f : Fin (n+1) → Fin 6 // Normal f ∧ ∀ i : Fin n,
  f i.castSucc≠f i.succ ∧ (f i.castSucc).val+(f i.succ).val≠5}

private theorem path_embedding {n : ℕ} (f : Fin (n+1) → Fin 6) :
    (Normal f ∧ ∀ i : Fin n, f i.castSucc≠f i.succ ∧ (f i.castSucc).val+(f i.succ).val≠5) ↔
      (emb6 (f 0)=0 ∧
       good8 (false,false,false) (emb6 ∘ f) ∧ ∀ i : Fin n,
       emb6 (f i.castSucc)≠emb6 (f i.succ) ∧ (emb6 (f i.castSucc)).val+(emb6 (f i.succ)).val≠7) := by
  rw [← good_embedding (false,false) f]
  simp only [HardinGraphNormalization.Normal,embedding_certificate.2.2.2.2.2.2,
    ← embedding_certificate.2.2.2.2.2.1]
  tauto

private noncomputable def sixSourceEquiv (n : ℕ) :
    Path6 n ≃ {f : Path8 n // ∀ i, (beta8 (f.val i)).val ≤ 2} where
  toFun f := ⟨⟨emb6 ∘ f.val,by
    have h := (path_embedding f.val).mp f.property
    exact ⟨h.1,by simpa using (good8_iff _ _).mp h.2.1,h.2.2⟩⟩,
    fun _ => embedding_certificate.2.2.1 _⟩
  invFun f := ⟨unemb6 ∘ f.val.val,by
    have he : emb6 ∘ (unemb6 ∘ f.val.val) = f.val.val := by
      funext i; exact embedding_certificate.2.1 _ (f.property i)
    apply (path_embedding _).mpr
    have hgood : good8 (false,false,false) f.val.val :=
      (good8_iff _ _).mpr (by simpa using f.val.property.2.1)
    have hh : (emb6 ∘ (unemb6 ∘ f.val.val)) 0 = 0 ∧
        good8 (false,false,false) (emb6 ∘ (unemb6 ∘ f.val.val)) ∧
        (∀ i : Fin n, (emb6 ∘ (unemb6 ∘ f.val.val)) i.castSucc ≠
          (emb6 ∘ (unemb6 ∘ f.val.val)) i.succ ∧
          ((emb6 ∘ (unemb6 ∘ f.val.val)) i.castSucc).val +
          ((emb6 ∘ (unemb6 ∘ f.val.val)) i.succ).val ≠ 7) := by
      rw [he]
      exact ⟨f.val.property.1,hgood,f.val.property.2.2⟩
    simpa only [Function.comp_apply] using hh⟩
  left_inv f := Subtype.ext (by funext i; exact embedding_certificate.1 _)
  right_inv f := Subtype.ext (Subtype.ext (by
    funext i; exact embedding_certificate.2.1 _ (f.property i)))

/-- Three pairs on a path correspond to at most two labels on independent vertices.
This restriction is transported through the same four-pair inverse, not by
replacing the original eight-colour source. -/
noncomputable def sixContractEquiv (n : ℕ) :
    Path6 (n+1) ≃ {f : Legal (⊥ : SimpleGraph (Fin (n+1))) //
      ∀ i, (beta (f.val i)).val < 2} := by
  let e := (pathEquiv n)
  let e6 := sixSourceEquiv (n+1)
  have hbound : ∀ f : Path8 (n+1),
      (∀ i, (beta8 (f.val i)).val ≤ 2) ↔ ∀ i, (beta ((e f).val i)).val < 2 := by
    intro f
    have h0 := f.property.1
    have hs := (sourceEquiv (n+1) f).property
    have h := contract_bound 0 0 (Fin.tail f.val) (by decide) hs
    change (∀ i, (beta8 (f.val i)).val ≤ 2) ↔
      ∀ i, (beta (contract 0 (Fin.tail f.val) i)).val < 2
    constructor
    · intro hb; exact h.mp (fun i => hb i.succ)
    · intro hb
      have ht := h.mpr hb
      intro i
      refine Fin.cases ?_ (fun j => ht j) i
      simp [h0,beta8]
  exact e6.trans (e.subtypeEquiv hbound)

private theorem one_row_normal {n : ℕ} (f : Fin (n+1) → Fin 6) :
    HardinA233251TriangleStrip.widthNormal (false,false) (fun _ : Fin 1 => f) ↔
      HardinA233175PairStrip.good (false,false) f := by
  rw [HardinA233175PairStrip.good_iff]
  change (∀ i : Fin 1, ∀ j,
    ((f j=2 ∨ f j=3 ∨ f j=4) → (false : Bool) = true ∨ ∃ r : Fin 1, ∃ k,
      (r < i ∨ r = i ∧ k < j) ∧ f k=1) ∧
    (f j=3 → (false : Bool) = true ∨ ∃ r : Fin 1, ∃ k, (r < i ∨ r = i ∧ k < j) ∧ f k=2)) ↔ _
  simp [Fin.forall_fin_one,Fin.exists_fin_one]

private theorem one_row_iff {n : ℕ} (f : Fin (n+1) → Fin 6) :
    HardinA233251TriangleStrip.widthLegal
      (fun c => HardinThinGraphTransport.proper (beta ∘ c))
      (fun c d => HardinThinGraphTransport.compatible true (beta ∘ c) (beta ∘ d))
      (fun a : Fin 1 × Fin (n+1) => f a.2) ↔
    (HardinGraphNormalization.Normal f ∧ ∀ i : Fin n,
      f i.castSucc ≠ f i.succ ∧ (f i.castSucc).val+(f i.succ).val ≠ 5) := by
  simp [HardinA233251TriangleStrip.widthLegal,Fin.exists_fin_one,Fin.forall_fin_one,
    one_row_normal]
  simp only [HardinThinGraphTransport.proper,Function.comp_apply,
    HardinA233251TriangleStrip.colour_bond_iff,HardinGraphNormalization.Normal]
  tauto

/-- The three-pair objects are precisely the existing literal one-row strip. -/
noncomputable def sixLiteralEquiv (n : ℕ) :
    Path6 n ≃ HardinThinGraphTransport.literalStrip true 0 n where
  toFun f := ⟨fun a => f.val a.2,(one_row_iff f.val).mpr f.property⟩
  invFun f := ⟨fun i => f.val (0,i),by
    have he : (fun a : Fin 1 × Fin (n+1) => f.val (0,a.2)) = f.val := by
      funext a; rcases a with ⟨i,j⟩; have hi : i = 0 := Fin.ext (by have := i.isLt; omega); subst i; rfl
    apply (one_row_iff _).mp
    rw [he]
    exact f.property⟩
  left_inv _ := rfl
  right_inv f := Subtype.ext (by funext a; rcases a with ⟨i,j⟩; have hi : i = 0 := Fin.ext (by have := i.isLt; omega); subst i; rfl)

private theorem ordered_two {n : ℕ} (p : Fin (n+1) → Fin 3) (hp : Ordered p) :
    (∀ i, (p i).val < 2) ↔ Fintype.card (Set.range p) ≤ 2 := by
  classical
  constructor
  · intro h
    let e : Set.range p ↪ Fin 2 :=
      ⟨fun c => ⟨c.val.val, by obtain ⟨i,hi⟩ := c.property; simpa [← hi] using h i⟩,
       by intro a b hab; apply Subtype.ext; apply Fin.ext; exact congrArg (fun c : Fin 2 => c.val) hab⟩
    simpa using Fintype.card_le_of_injective e e.injective
  · intro h i
    by_contra hi
    have hi2 : p i = 2 := Fin.ext (by have := (p i).isLt; omega)
    obtain ⟨j,_,hj⟩ := hp.2 i hi2
    have hr : Set.range p = Set.univ := by
      ext c
      simp only [Set.mem_univ,iff_true]
      fin_cases c
      · exact ⟨0,hp.1⟩
      · exact ⟨j,hj⟩
      · exact ⟨i,hi2⟩
    have he : Fintype.card (Set.range p) = 3 := by
      simpa using Fintype.card_congr (Equiv.cast (congrArg (fun s : Set (Fin 3) => ↥s) hr))
    omega

/-- Proper even-marked unlabelled partitions on n+1 vertices, with the actual
number of nonempty classes bounded by two. -/
noncomputable def sixMarkedPartitionEquiv (n : ℕ) :
    HardinThinGraphTransport.literalStrip true 0 (n+1) ≃
    {x : (Σ S : StablePartition (⊥ : SimpleGraph (Fin (n+1))),
      EvenMarking (((partitionEquiv (⊥ : SimpleGraph (Fin (n+1)))).symm S).val)) //
      Nat.card x.1.relation.classes ≤ 2} := by
  classical
  let e := (literalPartitionEquiv (⊥ : SimpleGraph (Fin (n+1)))).trans
    (Equiv.sigmaCongrRight fun _S => signMarkEquiv _)
  refine (sixLiteralEquiv (n+1)).symm.trans ((sixContractEquiv n).trans (e.subtypeEquiv ?_))
  intro f
  have hc : Nat.card (e f).1.relation.classes =
      Fintype.card (Set.range (beta ∘ f.val)) := by
    change Nat.card (Setoid.ker (beta ∘ f.val)).classes = _
    rw [← Nat.card_congr (Setoid.quotientEquivClasses (Setoid.ker (beta ∘ f.val))),
      Nat.card_congr (Setoid.quotientKerEquivRange (beta ∘ f.val)),Nat.card_eq_fintype_card]
  rw [hc]
  exact ordered_two (beta ∘ f.val) ((normal_iff f.val).mp f.property.1).1

/-- The literal source sequence, including its separate empty-series convention. -/
noncomputable def b : ℕ → ℕ
  | 0 => 0
  | m+1 => Nat.card (Path8 m)

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinMarkedPath
