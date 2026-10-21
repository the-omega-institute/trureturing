/- GID: D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.claim; result=D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result; claim=D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.claim
   digest: No finite set computes all Knutson indices in one rank-five ring. -/

/-
result: proof_shape: bind-only; escape_witness: none;
admission_basis: open-problem-resolution (#19214; Refuted).
Direct frozen dependencies: none.
All proof helpers are bind-only and are used in the derivation of result.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The source definitions use the expressions fixed in #19214.
-/
import Mathlib.RingTheory.FiniteType

set_option autoImplicit false
namespace D5.S3.HomologicalAlgebra.KnutsonFiniteSubindexRefutation

/-- `r` is regular for the dimension homomorphism `α`: `α(r) ≠ 0` and `x · r = α(x) r` for all `x`. -/
def IsRegularElement {R : Type*} [CommRing R] (α : R →+* ℤ) (r : R) : Prop :=
  α r ≠ 0 ∧ ∀ x : R, x * r = α x • r

/-- The Knutson Index `𝒦_r(x)`: the non-negative integer `m` with `Rx ∩ ℤr = mℤr`, that is, the least positive `m`
with `m r ∈ Rx`, and `0` when there is none. -/
noncomputable def knutsonIndex {R : Type*} [CommRing R] (r x : R) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∃ y : R, y * x = (m : ℤ) • r}

/-- `S(x) = {s ∈ S : s · x ∈ ℤr}`. -/
noncomputable def eligible {R : Type*} [CommRing R] (r : R) (S : Finset R) (x : R) : Finset R := by
  classical
  exact S.filter fun s => ∃ m : ℤ, s * x = m • r

/-- The index `m` with `s · x = m r`, for an eligible `s`. -/
noncomputable def eligibleIndex {R : Type*} [CommRing R] (r s x : R) : ℤ := by
  classical
  exact if h : ∃ m : ℤ, s * x = m • r then h.choose else 0

/-- The Knutson `S`-subindex `𝒦_r^S(x) = gcd Ind(x)`, with `Ind(x) = {m : s · x = m r, s ∈ S(x)}`, and `∞` when
`S(x) = ∅`. -/
noncomputable def knutsonSubindex {R : Type*} [CommRing R] (r : R) (S : Finset R) (x : R) : ℕ∞ :=
  if (eligible r S x).Nonempty then
    ((eligible r S x).gcd fun s => (eligibleIndex r s x).natAbs : ℕ)
  else ⊤

/-- Question 2.5, for every finitely generated commutative ring `R` with a dimension homomorphism `α` and a regular
element `r`: "Does there exist a finite subset S ⊂ R such that for all x ∈ R we have 𝒦_r(x) = 𝒦_r^S(x)?" -/
def claim : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (α : R →+* ℤ) (r : R), IsRegularElement α r →
    ∃ S : Finset R, ∀ x : R, (knutsonIndex r x : ℕ∞) = knutsonSubindex r S x

@[ext] private structure R where
  d : ℤ
  a : ℤ
  b : ℤ
  f : ℤ
  t : ℤ

private def c (x : R) : ℤ := x.d + 2*x.a + 2*x.b + 4*x.t

private instance zeroR : Zero R := ⟨⟨0,0,0,0,0⟩⟩
private instance oneR : One R := ⟨⟨1,0,0,0,0⟩⟩
private instance addR : Add R := ⟨fun x y => ⟨x.d+y.d,x.a+y.a,x.b+y.b,x.f+y.f,x.t+y.t⟩⟩
private instance negR : Neg R := ⟨fun x => ⟨-x.d,-x.a,-x.b,-x.f,-x.t⟩⟩
private instance mulR : Mul R := ⟨fun x y =>
  ⟨x.d*y.d,
   x.d*y.a+x.a*y.d,
   x.d*y.b+x.b*y.d,
   x.d*y.f+x.f*y.d+x.a*y.b+x.b*y.a,
   x.a*y.a+x.b*y.b+x.a*y.b+x.b*y.a+x.d*y.t+x.t*y.d+
     2*x.a*y.t+2*x.t*y.a+2*x.b*y.t+2*x.t*y.b+4*x.t*y.t⟩⟩

@[simp] private theorem d_zero : (0:R).d=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem a_zero : (0:R).a=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem b_zero : (0:R).b=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem f_zero : (0:R).f=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem t_zero : (0:R).t=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem d_one : (1:R).d=1 := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem a_one : (1:R).a=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem b_one : (1:R).b=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem f_one : (1:R).f=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem t_one : (1:R).t=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem d_add (x y:R) : (x+y).d=x.d+y.d := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem a_add (x y:R) : (x+y).a=x.a+y.a := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem b_add (x y:R) : (x+y).b=x.b+y.b := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem f_add (x y:R) : (x+y).f=x.f+y.f := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem t_add (x y:R) : (x+y).t=x.t+y.t := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem d_neg (x:R) : (-x).d=-x.d := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem a_neg (x:R) : (-x).a=-x.a := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem b_neg (x:R) : (-x).b=-x.b := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem f_neg (x:R) : (-x).f=-x.f := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem t_neg (x:R) : (-x).t=-x.t := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem d_mul (x y:R) : (x*y).d=x.d*y.d := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem a_mul (x y:R) : (x*y).a=x.d*y.a+x.a*y.d := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem b_mul (x y:R) : (x*y).b=x.d*y.b+x.b*y.d := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem f_mul (x y:R) : (x*y).f=x.d*y.f+x.f*y.d+x.a*y.b+x.b*y.a := Eq.symm (Int.neg_inj.mp rfl)
@[simp] private theorem t_mul (x y:R) : (x*y).t=x.a*y.a+x.b*y.b+x.a*y.b+x.b*y.a+x.d*y.t+x.t*y.d+
     2*x.a*y.t+2*x.t*y.a+2*x.b*y.t+2*x.t*y.b+4*x.t*y.t := Eq.symm (Int.neg_inj.mp rfl)

private instance addCommGroup : AddCommGroup R := by
  refine
    { sub := fun x y => x + -y
      nsmul := @nsmulRec R ⟨0⟩ ⟨(· + ·)⟩
      zsmul := @zsmulRec R ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
        (@nsmulRec R ⟨0⟩ ⟨(· + ·)⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]

private instance addGroupWithOne : AddGroupWithOne R :=
  { addCommGroup with
    natCast := fun n => ⟨n,0,0,0,0⟩
    intCast := fun z => ⟨z,0,0,0,0⟩ }

@[simp] private theorem d_intCast (z:ℤ) : (z:R).d=z := Int.neg_inj.mp rfl
@[simp] private theorem a_intCast (z:ℤ) : (z:R).a=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem b_intCast (z:ℤ) : (z:R).b=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem f_intCast (z:ℤ) : (z:R).f=0 := Int.neg_eq_zero.mp rfl
@[simp] private theorem t_intCast (z:ℤ) : (z:R).t=0 := Int.neg_eq_zero.mp rfl

private instance commRing : CommRing R := by
  refine
    { addGroupWithOne with
      npow := @npowRec R ⟨1,0,0,0,0⟩ ⟨(· * ·)⟩
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      add_comm := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;> simp <;> ring

private noncomputable def alpha : R →+* ℤ :=
  { toFun := c
    map_one' := by simp [c]
    map_zero' := by simp [c]
    map_add' := by intro x y; simp [c]; ring
    map_mul' := by intro x y; simp [c]; ring }

private def r : R := ⟨0,0,0,0,1⟩

private def coordMap : (Fin 5 → ℤ) →ₗ[ℤ] R where
  toFun v := ⟨v 0,v 1,v 2,v 3,v 4⟩
  map_add' v w := by ext <;> simp
  map_smul' z v := by ext <;> simp

private theorem coordMap_surjective : Function.Surjective coordMap := by
  intro x
  refine ⟨fun i => ![x.d,x.a,x.b,x.f,x.t] i, ?_⟩
  apply R.ext <;> rfl

private instance moduleFinite : Module.Finite ℤ R := Module.Finite.of_surjective coordMap coordMap_surjective


open scoped BigOperators

private lemma smul_r (m : ℤ) : m • r = ⟨0, 0, 0, 0, m⟩ := by
  ext <;> simp [r]

private def X (k : ℤ) : R := ⟨0, 1, 2*k, 0, -k⟩
private def Y (k : ℤ) : R := ⟨0, 1, -2*k, 0, k⟩

private lemma c_X (k : ℤ) : c (X k) = 2 := by simp [X, c]; ring

private lemma XY (k : ℤ) : X k * Y k = r := by
  ext <;> simp [X, Y, r]; ring

private lemma regular_r : IsRegularElement alpha r := by
  constructor
  · simp [alpha, r, c]
  · intro s
    change s * r = c s • r
    rw [smul_r]
    ext <;> simp [r, c]

private lemma eligible_equations {k m : ℤ} {s : R}
    (h : s * X k = m • r) :
    s.d = 0 ∧ s.b + 2*k*s.a = 0 ∧ c s = 2*m := by
  have ha := congrArg R.a h
  have hf := congrArg R.f h
  have hc0 := congrArg c h
  have hd' : s.d = 0 := by
    simpa [X, r, smul_eq_mul] using ha
  have hf' : s.b + 2*k*s.a = 0 := by
    simpa [X, r, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hf
  have hcmul : c (s * X k) = c s * c (X k) := by
    simpa [alpha] using (map_mul alpha s (X k))
  have hcr : c (m • r) = 4*m := by
    rw [smul_r]
    simp [c]
  have hc' : c s * 2 = 4*m := by
    calc
      c s * 2 = c (s * X k) := by rw [hcmul, c_X]
      _ = c (m • r) := hc0
      _ = 4*m := hcr
  have hc'': c s = 2*m := by nlinarith [hc']
  exact ⟨hd', hf', hc''⟩

private lemma even_of_eligible_of_zero {k m : ℤ} {s : R}
    (hd : s.d = 0) (ha : s.a = 0) (hb : s.b = 0)
    (h : s * X k = m • r) : Even m := by
  have hc := (eligible_equations h).2.2
  rw [c, hd, ha, hb] at hc
  exact ⟨s.t, by omega⟩

private lemma knutsonIndex_X (k : ℤ) : knutsonIndex r (X k) = 1 := by
  let A : Set ℕ := {m | 0 < m ∧ ∃ y : R, y * X k = (m : ℤ) • r}
  have hmem : 1 ∈ A := by
    refine ⟨zero_lt_one, ?_⟩
    refine ⟨Y k, ?_⟩
    simpa [mul_comm] using XY k
  have hne : A.Nonempty := ⟨1, hmem⟩
  have hinf := Nat.sInf_mem hne
  have hle := Nat.sInf_le hmem
  have hpos : 0 < sInf A := hinf.1
  change sInf A = 1
  omega

private lemma eligibleIndex_even {k : ℤ} {s : R}
    (hk : ∀ m : ℤ, s * X k = m • r →
      s.d = 0 ∧ s.a = 0 ∧ s.b = 0) :
    Even (eligibleIndex r s (X k)) := by
  classical
  unfold eligibleIndex
  split
  · rename_i h
    exact even_of_eligible_of_zero (hk _ h.choose_spec).1
      (hk _ h.choose_spec).2.1 (hk _ h.choose_spec).2.2 h.choose_spec
  · exact ⟨0, by simp⟩

private lemma subindex_ne_one_of_even {S : Finset R} {x : R}
    (heven : ∀ s ∈ eligible r S x,
      Even (eligibleIndex r s x)) :
    knutsonSubindex r S x ≠ 1 := by
  classical
  by_cases hne : (eligible r S x).Nonempty
  · simp only [knutsonSubindex, hne, ↓reduceIte]
    intro hone
    let T := eligible r S x
    let f : R → ℕ := fun s => (eligibleIndex r s x).natAbs
    have hdvd : 2 ∣ T.gcd f := by
      apply Finset.dvd_gcd
      intro s hs
      have hev : Even (eligibleIndex r s x) := heven s hs
      have hnat : Even (eligibleIndex r s x).natAbs := hev.natAbs
      exact hnat.two_dvd
    have hcast : ((T.gcd f : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) := by
      exact hone
    have hg : T.gcd f = 1 := WithTop.coe_eq_coe.mp hcast
    rw [hg] at hdvd
    norm_num at hdvd
  · simp [knutsonSubindex, hne]

/-- The counterexample refutes Question 2.5. -/
theorem result : ¬ claim := by
  classical
  intro hclaim
  obtain ⟨S, hS⟩ := hclaim R alpha r regular_r
  let K : ℕ := 1 + S.sum (fun s => s.b.natAbs)
  let k : ℤ := K
  let x : R := X k
  have heven : ∀ s ∈ eligible r S x,
      Even (eligibleIndex r s x) := by
    intro s hs
    have hsS : s ∈ S := (Finset.mem_filter.mp hs).1
    apply eligibleIndex_even
    intro m hm
    have heq := eligible_equations hm
    have hdiv : (2 * (K : ℤ)) ∣ s.b := by
      refine ⟨-s.a, ?_⟩
      have hb : s.b = -(2 * (K : ℤ) * s.a) :=
        eq_neg_of_add_eq_zero_left heq.2.1
      rw [hb]
      ring
    have hsum : s.b.natAbs ≤ S.sum (fun t => t.b.natAbs) := by
      exact Finset.single_le_sum (f := fun t : R => t.b.natAbs) (fun _ _ => Nat.zero_le _) hsS
    have hltN : s.b.natAbs < 2 * K := by
      dsimp [K]
      omega
    have hltZ : |s.b| < (2 * (K : ℤ)) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hltN
    have hb0 : s.b = 0 := Int.eq_zero_of_abs_lt_dvd hdiv hltZ
    have hka : (2 * (K : ℤ)) * s.a = 0 :=
      (eq_zero_iff_eq_zero_of_add_eq_zero heq.2.1).mp hb0
    have hKz : (2 * (K : ℤ)) ≠ 0 := by
      have : (0 : ℤ) < 2 * (K : ℤ) := by exact_mod_cast (Nat.pos_of_neZero (2 * K))
      exact ne_of_gt this
    have ha0 : s.a = 0 := (mul_eq_zero.mp hka).resolve_left hKz
    exact ⟨heq.1, ha0, hb0⟩
  have hsub : knutsonSubindex r S x ≠ 1 :=
    subindex_ne_one_of_even heven
  have hidx : knutsonIndex r x = 1 := knutsonIndex_X k
  have heq := hS x
  apply hsub
  rw [hidx] at heq
  exact heq.symm

end D5.S3.HomologicalAlgebra.KnutsonFiniteSubindexRefutation
