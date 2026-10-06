module

public import Init

public section

namespace LeanInformationAudit

/-- Publication metadata is bound by the elaborator. The kernel claim below
contains only ids; Name-level `ExactlyCovers` is not claimed from this certificate. -/
structure CensusKeyManifest where
  headSha : String
  reportSha256 : String
  censusRoot : Lean.Name
  keys : List Nat
  deriving Repr, Inhabited

/-- A chunk contains at most 100 base-2^256 digits, least significant id first.
The explicit arity preserves leading zero digits. The binder checks the domain,
arity and packed literal against each independent wire authority. -/
@[expose] def decodeIds : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, value => value % 2 ^ 256 :: decodeIds k (value / 2 ^ 256)

theorem decodeIds_length (k value : Nat) : (decodeIds k value).length = k := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih _)

/-- Exactly one Nat comparison per adjacent pair. -/
@[expose] def strictlyAscending : List Nat → Bool
  | a :: b :: rest => decide (a < b) && strictlyAscending (b :: rest)
  | _ => true

private theorem ascending_head {a : Nat} {xs : List Nat}
    (h : strictlyAscending (a :: xs) = true) : ∀ b, b ∈ xs → a < b := by
  induction xs generalizing a with
  | nil => intro b hb; cases hb
  | cons c cs ih =>
    have step : a < c ∧ strictlyAscending (c :: cs) = true := by
      simpa only [strictlyAscending, Bool.and_eq_true, decide_eq_true_eq] using h
    intro b hb
    cases List.mem_cons.mp hb with
    | inl eq => subst b; exact step.1
    | inr hb => exact Nat.lt_trans step.1 (ih step.2 b hb)

theorem strictlyAscending_nodup (xs : List Nat)
    (h : strictlyAscending xs = true) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · intro ha
      exact Nat.lt_irrefl a (ascending_head h a ha)
    · apply ih
      cases xs with
      | nil => rfl
      | cons b rest => exact (Bool.and_eq_true_iff.mp h).2

/-- Accounting over the id set: linear adjacent comparisons, requested count,
and equality with independently emitted report ids. Names, hex spelling and
metadata remain elaborator obligations; this is not Name-level `ExactlyCovers`.
Never decide `List.Nodup` or Finset equality here (quadratic). -/
@[expose] def CensusKeyManifest.Certificate (ids : List Nat) (requested : Nat)
    (reportIds : List Nat) : Prop :=
  strictlyAscending ids = true ∧ ids.length = requested ∧ ids = reportIds

/-- The top `b` bits of a validated 256-bit id. -/
@[expose] def idPrefix (b id : Nat) : Nat := id / 2 ^ (256 - b)

@[expose] def inRange (k b : Nat) : List Nat → Bool
  | [] => true
  | id :: ids => decide (idPrefix b id = k) && inRange k b ids

/-- One constructor per bucket, including empty buckets. Its indices ensure
that range order, the inventory lists, report lists and counts cannot drift. -/
inductive BucketCertificates (b : Nat) : Nat → List (List Nat) → List Nat → List (List Nat) → Prop
  | nil (k) : BucketCertificates b k [] [] []
  | cons {k inv rep n invs ns reps}
      (ascending : strictlyAscending inv = true) (range : inRange k b inv = true)
      (length : inv.length = n) (equality : inv = rep)
      (tail : BucketCertificates b (k + 1) invs ns reps) :
      BucketCertificates b k (inv :: invs) (n :: ns) (rep :: reps)

-- Direct Boolean recursion retains the flat certificate's [propext] closure;
-- Init's pairwise_append / all_eq_true additionally depend on Quot.sound.
private theorem ascending_append {xs ys : List Nat}
    (hx : strictlyAscending xs = true) (hy : strictlyAscending ys = true)
    (cross : ∀ x ∈ xs, ∀ y ∈ ys, x < y) : strictlyAscending (xs ++ ys) = true := by
  induction xs with
  | nil => exact hy
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (cross a (by simp) b (by simp)), hy⟩
    | cons b xs =>
      have parts := Bool.and_eq_true_iff.mp hx
      exact Bool.and_eq_true_iff.mpr ⟨parts.1, ih parts.2
        (fun x mem y hy => cross x (List.mem_cons_of_mem a mem) y hy)⟩

private theorem range_prefix {k b : Nat} {ids : List Nat} (h : inRange k b ids = true)
    {id : Nat} (mem : id ∈ ids) : idPrefix b id = k := by
  induction ids with
  | nil => cases mem
  | cons x xs ih =>
    have parts := Bool.and_eq_true_iff.mp h
    rcases List.mem_cons.mp mem with eq | mem
    · subst id; exact of_decide_eq_true parts.1
    · exact ih parts.2 mem

private theorem flatten_prefix_lower {b k invs ns reps}
    (h : BucketCertificates b k invs ns reps) :
    ∀ id ∈ invs.flatten, k ≤ idPrefix b id := by
  induction h with
  | nil => intro id mem; cases mem
  | @cons k inv rep n invs ns reps ordered range length equality tail ih =>
    intro id mem
    rcases List.mem_append.mp mem with mem | mem
    · exact Nat.le_of_eq (range_prefix range mem).symm
    · exact Nat.le_trans (Nat.le_succ k) (ih id mem)

/-- Join checked ranges without decoding or comparing any concrete ids. -/
theorem strictlyAscending_flatten_of_ranges {b k invs ns reps}
    (h : BucketCertificates b k invs ns reps) : strictlyAscending invs.flatten = true := by
  induction h with
  | nil => rfl
  | @cons k inv rep n invs ns reps ordered range length equality tail ih =>
    apply ascending_append ordered ih
    intro x hx y hy
    have px := range_prefix range hx
    have py := flatten_prefix_lower tail y hy
    apply Nat.lt_of_not_ge
    intro hyx
    have le : idPrefix b y ≤ idPrefix b x := Nat.div_le_div_right hyx
    rw [px] at le
    exact Nat.not_succ_le_self k (Nat.le_trans py le)

/-- The generic list identity is in Init; only the per-bucket length equations
are substituted here. The assembly decides the sum of `N` count literals. -/
theorem length_flatten {b k invs ns reps} (h : BucketCertificates b k invs ns reps) :
    invs.flatten.length = ns.sum := by
  rw [List.length_flatten]
  induction h with
  | nil => rfl
  | cons ordered range length equality tail ih =>
    simp only [List.map_cons, List.sum_cons, length, ih]

theorem bucket_congruence {b k invs ns reps} (h : BucketCertificates b k invs ns reps) :
    invs = reps := by
  induction h with
  | nil => rfl
  | cons ordered range length equality tail ih => cases equality; cases ih; rfl

theorem certificate_of_buckets {b k invs ns reps requested}
    (h : BucketCertificates b k invs ns reps) (total : ns.sum = requested) :
    CensusKeyManifest.Certificate invs.flatten requested reps.flatten :=
  ⟨strictlyAscending_flatten_of_ranges h, (length_flatten h).trans total,
    congrArg List.flatten (bucket_congruence h)⟩

/-- Half-open bounds allow a binary range tree with bounded leaves. -/
@[expose] def boundedRange (lo hi : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => (decide (lo ≤ x) && decide (x < hi)) && boundedRange lo hi xs

@[expose] def RangeCertificate (lo hi : Nat) (ids : List Nat) (n : Nat)
    (report : List Nat) : Prop :=
  strictlyAscending ids = true ∧ boundedRange lo hi ids = true ∧ ids.length = n ∧ ids = report

private theorem bounded_member {lo hi : Nat} {xs : List Nat}
    (h : boundedRange lo hi xs = true) {x : Nat} (hx : x ∈ xs) : lo ≤ x ∧ x < hi := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    have parts := Bool.and_eq_true_iff.mp h
    rcases List.mem_cons.mp hx with eq | mem
    · subst x
      exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp parts.1).1,
        of_decide_eq_true (Bool.and_eq_true_iff.mp parts.1).2⟩
    · exact ih parts.2 mem

private theorem bounded_of_members {lo hi : Nat} {xs : List Nat}
    (h : ∀ x ∈ xs, lo ≤ x ∧ x < hi) : boundedRange lo hi xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have head := h x (List.mem_cons_self)
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true head.1, decide_eq_true head.2⟩,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

/-- A node uses only the two child certificates and their adjacent bounds.
No concrete id is decoded, compared, or counted by a composition process. -/
theorem range_join {lo mid hi : Nat} {left right lreport rreport : List Nat} {ln rn : Nat}
    (hl : RangeCertificate lo mid left ln lreport)
    (hr : RangeCertificate mid hi right rn rreport)
    (order : lo ≤ mid ∧ mid ≤ hi) :
    RangeCertificate lo hi (left ++ right) (ln + rn) (lreport ++ rreport) := by
  refine ⟨ascending_append hl.1 hr.1 ?_, bounded_of_members ?_, ?_, ?_⟩
  · intro x hx y hy
    exact Nat.lt_of_lt_of_le (bounded_member hl.2.1 hx).2 (bounded_member hr.2.1 hy).1
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h := bounded_member hl.2.1 hx
      exact ⟨h.1, Nat.lt_of_lt_of_le h.2 order.2⟩
    · have h := bounded_member hr.2.1 hx
      exact ⟨Nat.le_trans order.1 h.1, h.2⟩
  · rw [List.length_append, hl.2.2.1, hr.2.2.1]
  · rw [hl.2.2.2, hr.2.2.2]

theorem certificate_of_range {lo hi : Nat} {ids report : List Nat} {n : Nat}
    (h : RangeCertificate lo hi ids n report) : CensusKeyManifest.Certificate ids n report :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

end LeanInformationAudit
