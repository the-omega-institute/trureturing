import D5.S1.Words.Attractors.PeriodicPrefixAttractors
import Reg.Support.DependentFamily
import Reg.D5.S1.Words.Attractors.FiniteWordAttractors

open _root_.D5.S1.Words.Attractors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
namespace Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits
open _root_.D5.S1.Words.Powers
open _root_.Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits
noncomputable section

namespace Endpoints
abbrev signature : Signature where
  Params := Σ _k : Nat, Nat → Nat
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Finset Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p n => (Finset.Icc (n+1-p.1) n).image (fun j => p.2 j-1)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (k : Nat) (hk : 2 ≤ k)
    (w : Nat → List α) (U : Nat → Nat)
    (hlen : ∀ m, (w m).length = m)
    (hprefix : ∀ m n, m ≤ n → w m = (w n).take m)
    (hU0 : U 0 = 1) (hU : StrictMono U)
    (hgaps : Monotone fun n => U (n + 1) - U n)
    (hperiod : ∀ n, List.HasPeriod (w (U (n + 1) - 1)) (U n))
    (hsuffix : ∀ n, k ≤ n → w (U (n - k)) <:+ w (U n)),
let B := fun n => U (n + 1) - 1
    let Δ := fun n => B n - U n
    let P := fun n => U n + if n < k then 0 else Δ (n - k)
    let Γ := fun n => (Finset.Icc (n + 1 - k) n).image fun j => U j - 1
    ∀ n, P n ≤ B n ∧ ∀ m, P n ≤ m → m ≤ B n → IsAttractor (w m) (R.readout () ⟨k,U⟩ n)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let w : Nat → List (ULift.{u} Nat) := fun m => List.replicate m ⟨0⟩
  let U : Nat → Nat := fun n => n+1
  have hpref : ∀ m n, m ≤ n → w m = (w n).take m := by
    intro m n hmn
    simp [w, List.take_replicate, Nat.min_eq_left hmn]
  have hper : ∀ n, List.HasPeriod (w (U (n+1)-1)) (U n) := by
    intro n
    apply List.hasPeriod_of_length_le
    simp [w,U]
  have hsuf : ∀ n, 2 ≤ n → w (U (n-2)) <:+ w (U n) := by
    intro n hn
    refine ⟨List.replicate (U n - U (n-2)) ⟨0⟩, ?_⟩
    dsimp [w]
    rw [← List.replicate_add]
    congr 1
    dsimp [U]
    omega
  have hh := h 2 (by omega) w U (by intro m; simp [w]) hpref rfl
    (by intro a b hab; dsimp [U]; omega)
    (by intro a b hab; dsimp [U]; omega) hper hsuf
  have hhit := (hh 0).2 1 (by decide) (by decide)
  exact no_empty_attractor _ (by simp [w]) hhit

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nested_word_endpoint_attractors, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨2,fun n => n+1⟩,0,1,by cases i; decide⟩

register_information_theorem nested_word_endpoint_attractors in arena
  readout via (realize signature (fun _ p n => (Finset.Icc (n+1-p.1) n).image (fun j => p.2 j-1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors
    coordinates := #[1,4]
    readouts := #[{path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","body","body","arg"], stateBinder := 16}] })
  escape continues (open)


end Endpoints

namespace Scan
abbrev signature : Signature where
  Params := Σ _α : Type u, Nat
  State := fun p => List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p W => W.drop p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ W => W) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (w : Nat → List α) (U b : Nat → Nat)
    (hlen : ∀ m, (w m).length = m)
    (hprefix : ∀ m n, m ≤ n → w m = (w n).take m)
    (hU : StrictMono U) (hpos : ∀ n, 0 < U n)
    (hperiod : ∀ n, List.HasPeriod (w (U (n + 1) - 1)) (U n))
    (count t N r : Nat) (X W : List α)
    (hcount : 0 < count)
    (hX : X <+: w (U (t + 1) - 1))
    (hR : X.length < U (t + 1) - 1) (hr : r ≤ X.length)
    (hstack : W = descendingBlocks w U b count t ++ X)
    (hsize : W.length = N + r)
    (htop : U (t + count) - 1 < W.length),
∃ h p, t ≤ h ∧ h < t + count ∧ U h ≤ p ∧ p ≤ N ∧
      p - U h + (U (h + 1) - 1) ≤ W.length ∧
      (W.drop (p - U h)).take (U (h + 1) - 1) = w (U (h + 1) - 1) ∧
      R.readout () ⟨α,p⟩ W <+: w (U (h + 1) - 1)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let w : Nat → List (ULift.{u} Nat) := fun m => List.replicate m ⟨0⟩
  let U : Nat → Nat := fun n => n+1
  have hpref : ∀ m n, m ≤ n → w m = (w n).take m := by
    intro m n hmn
    simp [w,List.take_replicate,Nat.min_eq_left hmn]
  have hper : ∀ n, List.HasPeriod (w (U (n+1)-1)) (U n) := by
    intro n
    apply List.hasPeriod_of_length_le
    simp [w,U]
  obtain ⟨h,p,hlo,hhi,hrest⟩ := hh w U (fun _ => 2)
    (by intro m; simp [w]) hpref
    (by intro a b hab; dsimp [U]; omega) (by intro n; dsimp [U]; omega) hper
    1 0 2 0 [] ([⟨0⟩,⟨0⟩] : List (ULift.{u} Nat)) (by omega) (by exact List.nil_prefix)
    (by decide) (by decide) (by rfl) (by rfl) (by decide)
  have heq : h = 0 := by omega
  subst h
  have hlen := hrest.2.2.2.2.length_le
  change 2 ≤ 1 at hlen
  omega

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@periodic_residual_scan, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Nat,0⟩,[],[⟨0⟩],by cases i; decide⟩

register_information_theorem periodic_residual_scan in arena
  readout via (realize signature (fun _ p W => W.drop p.2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors
    coordinates := #[0,23]
    readouts := #[{path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","arg","arg","arg","fn","arg"], stateBinder := 14}] })
  escape continues (open)


end Scan

end
end Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits
