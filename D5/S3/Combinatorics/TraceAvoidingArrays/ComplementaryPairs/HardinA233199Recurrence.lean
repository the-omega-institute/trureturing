/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal width-five A233199 recurrence with all ten signed lags. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip

/-! OEIS A233199 revision 6, as pinned at
https://raw.githubusercontent.com/oeis/oeisdata/d4ade8b4ca7c6ff0ac8931532918fd4f6176805e/seq/A233/A233199.seq
The state retains both the boundary pattern and the historical first-use stage.
-/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence

open scoped BigOperators
open HardinA233196Strip (Seen allowed advance good finish beta widthLegal
  widthV widthStep widthTotal width_counting_bridge colour_bond_iff)

private abbrev Row := Fin 5 → Fin 8
private abbrev Boundary := Fin 5 → Fin 4

private abbrev Bond (a b : Fin 8) : Prop := a ≠ b ∧ a.val + b.val ≠ 7

private def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 4, Bond (c j.castSucc) (c j.succ)

private def bonds (c d : Row) : Prop :=
  (∀ j : Fin 5, Bond (c j) (d j)) ∧
    ∀ j : Fin 4, Bond (c j.succ) (d j.castSucc)

private instance (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ j : Fin 4, Bond (c j.castSucc) (c j.succ)))

private instance (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

/-- The literal count, with the anchor, all contained bonds and strict row-major first use. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n × Fin 5 → Fin 8 => widthLegal rowLegal bonds f)).card

private def pairs (c : Row) : Boundary := fun j => beta (c j)

private def proper (p : Boundary) : Prop :=
  ∀ j : Fin 4, p j.castSucc ≠ p j.succ

private instance (p : Boundary) : Decidable (proper p) :=
  inferInstanceAs (Decidable (∀ j : Fin 4, p j.castSucc ≠ p j.succ))

private def compatible (p : Boundary) (c : Row) : Prop :=
  (∀ j : Fin 5, p j ≠ beta (c j)) ∧
    ∀ j : Fin 4, p j.succ ≠ beta (c j.castSucc)

private instance (p : Boundary) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, colour_bond_iff, compatible, pairs]

private theorem row_iff (c : Row) : rowLegal c ↔ proper (pairs c) := by
  simp only [rowLegal, proper, pairs, colour_bond_iff]

private abbrev continuation := widthV rowLegal pairs compatible

private theorem counting_bridge (n : ℕ) :
    (a (n + 1) : ℤ) = widthTotal rowLegal pairs (continuation n) :=
  width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

private def stage (s : Seen) : Fin 4 :=
  if s.2.2 then 3 else if s.2.1 then 2 else if s.1 then 1 else 0

private def seen (k : Fin 4) : Seen :=
  (decide (1 ≤ k.val), decide (2 ≤ k.val), decide (3 ≤ k.val))

private def coherent (s : Seen) : Prop := seen (stage s) = s
private instance (s : Seen) : Decidable (coherent s) :=
  inferInstanceAs (Decidable (seen (stage s) = s))

private def bounded (k : Fin 4) (p : Boundary) : Prop := ∀ j, (p j).val ≤ k.val
private instance (k : Fin 4) (p : Boundary) : Decidable (bounded k p) :=
  inferInstanceAs (Decidable (∀ j, (p j).val ≤ k.val))

private theorem cell_valid : ∀ (s : Seen) (x : Fin 8), coherent s → allowed s x →
    coherent (advance s x) ∧ (stage s).val ≤ (stage (advance s x)).val ∧
      (beta x).val ≤ (stage (advance s x)).val := by
  decide +kernel

private theorem row_valid {k : ℕ} (s : Seen) (c : Fin k → Fin 8)
    (hs : coherent s) (hc : good s c) :
    coherent (finish s c) ∧ (stage s).val ≤ (stage (finish s c)).val ∧
      ∀ j, (beta (c j)).val ≤ (stage (finish s c)).val := by
  induction k generalizing s with
  | zero => exact ⟨hs, le_rfl, fun j => Fin.elim0 j⟩
  | succ k ih =>
    obtain ⟨hs', hmono, hhead⟩ := cell_valid s (c 0) hs hc.1
    obtain ⟨ht, hmono', htail⟩ := ih (advance s (c 0)) (Fin.tail c) hs' hc.2
    refine ⟨ht, hmono.trans hmono', ?_⟩
    rw [Fin.forall_fin_succ]
    exact ⟨hhead.trans hmono', htail⟩

private def names (p : Boundary) : List (Fin 4) :=
  ((List.ofFn p) ++ List.finRange 4).eraseDups

private def rename (p : Boundary) (x : Fin 4) : Fin 4 :=
  Fin.ofNat 4 ((names p).idxOf x)

private def rowCode (p : Boundary) : ℕ :=
  (p 0).val + 4 * (p 1).val + 16 * (p 2).val + 64 * (p 3).val + 256 * (p 4).val

private abbrev State := Fin 23

private def stageOf : State → Fin 4 := ![1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

private def rowCodeOf : State → Nat := ![68, 68, 580, 132, 388, 292, 548, 100, 612, 68, 580, 132, 388, 900, 292, 548, 804, 100, 612, 868, 228, 484, 740]

private def T : Matrix State State ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 16, 16, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 16, 16, 0, 16, 16, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 16, 0, 16, 16, 0, 16, 32, 32, 0],
    ![0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 16, 0, 48, 16, 48, 16, 0, 16, 32, 32, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 16, 16, 0, 0, 16, 16, 0, 32, 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 16, 16, 16, 32, 16, 0, 16, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 32, 32, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 32, 32, 0, 32, 32, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 32, 0, 32, 32, 0, 32, 64, 64, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 64, 0, 0, 0, 0, 0, 0, 32, 32, 64],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 128, 32, 96, 32, 0, 32, 64, 64, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 32, 32, 0, 0, 32, 32, 0, 64, 64],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 64, 64, 64, 64, 0, 0, 0, 32, 64, 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 32, 32, 32, 64, 32, 0, 32, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 0, 0, 0, 0, 0, 0, 64, 64, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 32, 32, 32, 32, 64, 32, 0, 32, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 64, 64, 0, 0, 0, 64, 32, 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 32, 64, 64, 0, 64, 64, 64, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 64, 32, 0, 64, 64]]

private def initial : State → ℤ := ![8, 0, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 2, 2]

private def powers : Fin 12 → State → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![16, 64, 96, 96, 160, 272, 160, 128, 96, 128, 192, 192, 320, 256, 512, 320, 448, 256, 192, 320, 320, 448, 256],
    ![2560, 10240, 22528, 28672, 57344, 101888, 52224, 44032, 21504, 20480, 45056, 57344, 114688, 77824, 202752, 104448, 165888, 88064, 43008, 104448, 124928, 174080, 75776],
    ![524288, 2097152, 6684672, 9764864, 21299200, 38027264, 18022400, 15466496, 5767168, 4194304, 13369344, 19529728, 42598400, 26738688, 76021760, 36044800, 60162048, 30932992, 11534336, 35651584, 46268416, 64880640, 24903680],
    ![140509184, 562036736, 2277507072, 3466592256, 7795113984, 13946585088, 6415187968, 5523898368, 1790967808, 1124073472, 4555014144, 6933184512, 15590227968, 9588178944, 27892121600, 12830375936, 21890072576, 11047796736, 3581935616, 12641632256, 16856907776, 23676846080, 8615100416],
    ![45432700928, 181730803712, 812956778496, 1246010277888, 2833000693760, 5077607645184, 2304853934080, 1995414962176, 610019573760, 363461607424, 1625913556992, 2492020555776, 5666001387520, 3459864592384, 10155181735936, 4609707868160, 7949044940800, 3990829924352, 1220039147520, 4559376220160, 6119388872704, 8599464050688, 3053990182912],
    ![15915001315328, 63660005261312, 293273251872768, 450140489908224, 1028002569781248, 1843576593973248, 832147766116352, 722641132453888, 216771294396416, 127320010522624, 586546503745536, 900280979816448, 2056005139562496, 1250514087968768, 3687152114204672, 1664295532232704, 2881661062610944, 1445282264907776, 433542588792832, 1650908119171072, 2218243234201600, 3120366754988032, 1097510173016064],
    ![5710932114145280, 22843728456581120, 106086516844920832, 162984937912270848, 372776154538442752, 668601355719409664, 301247013276614656, 261788083576373248, 78124286883135488, 45687456913162240, 212173033689841664, 325969875824541696, 745552309076885504, 452693401289097216, 1337202677079080960, 602494026553229312, 1044343769291292672, 523576167152746496, 156248573766270976, 598098316504334336, 803858586064125952, 1131477591891378176, 396768941365526528],
    ![2062883924824031232, 8251535699296124928, 38420080877748879360, 59056698071244079104, 135126647533438238720, 242371281625162973184, 109152941525090435072, 94859552047769845760, 28264868338307432448, 16503071398592249856, 76840161755497758720, 118113396142488158208, 270253295066876477440, 164011695405392723968, 484742562150814318592, 218305883050180870144, 378500962489330565120, 189719104095539691520, 56529736676614864896, 216724816115764559872, 291329428839435599872, 410137949427143278592, 143701270326509830144],
    ![746745865232720068608, 2986983460930880274432, 13921126488498329616384, 21402623634920230092800, 48975822281503544442880, 87848390210796289785856, 39557570059360727465984, 34377910111021463240704, 10237637419821581729792, 5973966921861760548864, 27842252976996659232768, 42805247269840460185600, 97951644563007088885760, 59436796795652382130176, 175696780386408207482880, 79115140118721454931968, 137181932619053500727296, 68755820222042926481408, 20475274839643163459584, 78542067339975209254912, 105587100570021626118144, 148651458925985638907904, 52069818658298886356992],
    ![270529759190867358253056, 1082119036763469433012224, 5045039862050330108755968, 7756798518394612822835200, 17750569782277470769119232, 31839679327097269983903744, 14336459354978634155687936, 12459451477931962270744576, 3709614468129522643369984, 2164238073526938866024448, 10090079724100660217511936, 15513597036789225645670400, 35501139564554941538238464, 21540962544957567352700928, 63679358653068640060964864, 28672918709957268311375872, 49719181633471265875427328, 24918902955863924541489152, 7419228936259045286739968, 28465491859773042850791424, 38268261919126211321135104, 53876551700227324171517952, 18870111757115952421928960],
    ![98034542381020792668291072, 392138169524083170673164288, 1828429138231369957189353472, 2811282333703888726151659520, 6433396783075649783966203904, 11539786510071355706397687808, 5195920986801419470090797056, 4515673520437635208221556736, 1344380150235068405737586688, 784276339048166341346328576, 3656858276462739914378706944, 5622564667407777452303319040, 12866793566151299567932407808, 7807015723283534659788472320, 23079573020106682615776411648, 10391841973602838940181594112, 18019795177238917707632476160, 9031347040875270416443113472, 2688760300470136811475173376, 10316713504106215578926055424, 13869635369234881527400103936, 19526648793794775232479756288, 6838917747290931556884938752]]

private def coeff : Fin 10 → ℤ := ![18446744073709551616, -1423137482249076736, 35184372088832000, -116548232544256, -10685878632448, 270851375104, -3665821696, 33062912, -203776, 736]

private def representative (i : State) : Boundary :=
  fun j => Fin.ofNat 4 (rowCodeOf i / 4 ^ j.val)

private def classOf (s : Seen) (p : Boundary) : State :=
  let code := rowCode (fun j => rename p (p j))
  ((List.finRange 23).find? (fun i => stageOf i == stage s && rowCodeOf i == code)).getD 0

private def fixesUnseen (k : Fin 4) (π : Fin 4 → Fin 4) : Prop :=
  ∀ x, k.val < x.val → π x = x

private instance (k : Fin 4) (π : Fin 4 → Fin 4) : Decidable (fixesUnseen k π) :=
  inferInstanceAs (Decidable (∀ x, k.val < x.val → π x = x))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem class_spec : ∀ (s : Seen) (p : Boundary),
    coherent s → proper p → bounded (stage s) p →
    Function.Bijective (rename p) ∧ fixesUnseen (stage s) (rename p) ∧
      stageOf (classOf s p) = stage s ∧
        (∀ j, representative (classOf s p) j = rename p (p j)) := by
  decide +kernel

private theorem power_table (k : Fin 12) :
    (T ^ k.val).mulVec (1 : State → ℤ) = powers k :=
  TransferMatrix.tabulatedPowers T 11 powers (by decide +kernel) (by decide +kernel) k

set_option maxRecDepth 20000 in
private theorem vector_relation :
    (T ^ (1 + 10)).mulVec (1 : State → ℤ) =
      ∑ j : Fin 10, coeff j • (T ^ (1 + j.val)).mulVec (1 : State → ℤ) := by
  have h (j : Fin 10) :
      (T ^ (1 + j.val)).mulVec (1 : State → ℤ) =
        powers (⟨1 + j.val, by omega⟩ : Fin 12) := power_table ⟨1 + j.val, by omega⟩
  rw [show (T ^ (1 + 10)).mulVec (1 : State → ℤ) = powers 11 from power_table 11]
  simp_rw [h]
  decide +kernel

/-- Relabel pairs while retaining the signed representative of each literal colour. -/
private def recolour (π : Fin 4 → Fin 4) (x : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (if x.val < 4 then (π (beta x)).val else 7 - (π (beta x)).val)

private theorem beta_recolour : ∀ (π : Fin 4 → Fin 4) (x : Fin 8),
    beta (recolour π x) = π (beta x) := by decide +kernel

private theorem recolour_bijective : ∀ (π : Fin 4 → Fin 4), Function.Bijective π →
    Function.Bijective (recolour π) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem cell_recolour : ∀ (π : Fin 4 → Fin 4) (k : Fin 4) (s : Seen) (x : Fin 8),
    Function.Bijective π → fixesUnseen k π → coherent s → k.val ≤ (stage s).val →
    (allowed s (recolour π x) ↔ allowed s x) ∧ advance s (recolour π x) = advance s x := by
  decide +kernel

private theorem row_recolour {d : ℕ} (π : Fin 4 → Fin 4) (k : Fin 4)
    (hπ : Function.Bijective π) (hfix : fixesUnseen k π) (s : Seen)
    (hs : coherent s) (hk : k.val ≤ (stage s).val) (c : Fin d → Fin 8) :
    (good s (fun j => recolour π (c j)) ↔ good s c) ∧
      (good s c → finish s (fun j => recolour π (c j)) = finish s c) := by
  induction d generalizing s with
  | zero => simp [good, finish]
  | succ d ih =>
    obtain ⟨ha, hf⟩ := cell_recolour π k s (c 0) hπ hfix hs hk
    have ht : Fin.tail (fun j => recolour π (c j)) =
        fun j : Fin d => recolour π (Fin.tail c j) := by
      funext j
      rfl
    simp only [good, finish, ha, hf, ht]
    by_cases hx : allowed s (c 0)
    · obtain ⟨hs', hmono, _⟩ := cell_valid s (c 0) hs hx
      simpa only [hx, true_and] using ih _ hs' (hk.trans hmono) (Fin.tail c)
    · simp [hx]

private theorem continuation_recolour (n : ℕ) (π : Fin 4 → Fin 4) (k : Fin 4)
    (hπ : Function.Bijective π) (hfix : fixesUnseen k π) (s : Seen)
    (hs : coherent s) (hk : k.val ≤ (stage s).val) (p : Boundary) :
    continuation n s (fun j => π (p j)) = continuation n s p := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    change widthStep rowLegal pairs compatible (continuation n) s (fun j => π (p j)) =
      widthStep rowLegal pairs compatible (continuation n) s p
    unfold widthStep
    let e : Equiv.Perm (Fin 8) := Equiv.ofBijective (recolour π) (recolour_bijective π hπ)
    let E : Row ≃ Row := Equiv.arrowCongr (Equiv.refl (Fin 5)) e
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro c _
    change (if rowLegal (fun j => recolour π (c j)) ∧
        compatible (fun j => π (p j)) (fun j => recolour π (c j)) ∧
        good s (fun j => recolour π (c j)) then
        continuation n (finish s (fun j => recolour π (c j)))
          (pairs (fun j => recolour π (c j))) else 0) = _
    obtain ⟨hg, hf⟩ := row_recolour π k hπ hfix s hs hk c
    have hpairs : pairs (fun j => recolour π (c j)) = fun j => π (pairs c j) := by
      funext j
      exact beta_recolour π (c j)
    simp only [row_iff, hpairs, proper, compatible, beta_recolour, hπ.1.ne_iff, hg]
    by_cases hc : good s c
    · obtain ⟨hs', hmono, _⟩ := row_valid s c hs hc
      rw [hf hc, ih _ hs' (hk.trans hmono)]
    · simp [hc]

/-- The five-column enumeration prunes a row as soon as a literal cell fails. -/
private def cellBonds (prev : Option (Fin 4)) (x : Fin 8) : Prop :=
  match prev with
  | none => True
  | some p => p ≠ beta x

private instance (prev : Option (Fin 4)) (x : Fin 8) : Decidable (cellBonds prev x) := by
  cases prev <;> unfold cellBonds <;> infer_instance

private def pathOK : {d : ℕ} → Option (Fin 4) → (Fin d → Fin 8) → Prop
  | 0, _, _ => True
  | _ + 1, prev, c => cellBonds prev (c 0) ∧ pathOK (some (beta (c 0))) (Fin.tail c)

private instance {d : ℕ} (prev : Option (Fin 4)) (c : Fin d → Fin 8) :
    Decidable (pathOK prev c) := by
  induction d generalizing prev with
  | zero => exact isTrue trivial
  | succ d ih =>
    change Decidable (cellBonds prev (c 0) ∧ pathOK (some (beta (c 0))) (Fin.tail c))
    haveI := ih (some (beta (c 0))) (Fin.tail c)
    infer_instance

private def scan : {d : ℕ} → (Fin d → Fin 8 → Bool) → Option (Fin 4) →
    Seen → ((Fin d → Fin 8) → Seen → ℤ) → ℤ
  | 0, _, _, s, H => H Fin.elim0 s
  | d + 1, pass, prev, s, H =>
      ∑ x : Fin 8, if pass 0 x = true ∧ cellBonds prev x ∧ allowed s x then
        scan (fun j : Fin d => pass j.succ) (some (beta x)) (advance s x)
          (fun c t => H (Fin.cons x c) t) else 0

private theorem scan_eq {d : ℕ} (pass : Fin d → Fin 8 → Bool)
    (prev : Option (Fin 4)) (s : Seen) (H : (Fin d → Fin 8) → Seen → ℤ) :
    scan pass prev s H = ∑ c : Fin d → Fin 8,
      if (∀ j, pass j (c j) = true) ∧ pathOK prev c ∧ good s c then H c (finish s c) else 0 := by
  classical
  induction d generalizing s prev with
  | zero =>
    simp only [scan, pathOK, good, finish, Fin.forall_fin_zero, and_self, ite_true]
    rw [Finset.sum_eq_single Fin.elim0]
    · intro c _ hn
      exact (hn (funext fun j => Fin.elim0 j)).elim
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  | succ d ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Fin 8)).sum_comp, Fintype.sum_prod_type]
    simp only [scan, Fin.consEquiv, Equiv.coe_fn_mk, pathOK, good, finish,
      Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : pass 0 x = true ∧ cellBonds prev x ∧ allowed s x
    · rw [ite_eq_left hx, ih]
      simp only [hx.1, hx.2.1, hx.2.2, true_and]
    · rw [ite_eq_right hx]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro c _
      exact ite_eq_right (fun h => hx ⟨h.1.1, h.2.1.1, h.2.2.1⟩)

private theorem pathOK_iff (c : Row) : pathOK none c ↔ rowLegal c := by
  simp [pathOK, cellBonds, row_iff, proper, pairs, Fin.forall_fin_succ, Fin.tail]

private def incoming (p : Boundary) (j : Fin 5) (x : Fin 8) : Bool :=
  decide (p j ≠ beta x ∧ ∀ h : j.val + 1 < 5, p ⟨j.val + 1, h⟩ ≠ beta x)

private theorem incoming_iff (p : Boundary) (c : Row) :
    (∀ j, incoming p j (c j) = true) ↔ compatible p c := by
  simp only [incoming, decide_eq_true_eq, compatible]
  constructor
  · intro h
    refine ⟨fun j => (h j).1, fun j => (h j.castSucc).2 ?_⟩
    change j.val + 1 < 5
    have := j.isLt
    omega
  · intro h j
    refine ⟨h.1 j, fun hj => ?_⟩
    exact h.2 ⟨j.val, by omega⟩

private def anchored (j : Fin 5) (x : Fin 8) : Bool := decide (j = 0 → x = 0)

private theorem anchored_iff (c : Row) : (∀ j, anchored j (c j) = true) ↔ c 0 = 0 := by
  simp only [anchored, decide_eq_true_eq]
  exact ⟨fun h => h 0 rfl, fun h j hj => hj ▸ h⟩

private def countTo (pass : Fin 5 → Fin 8 → Bool) (s : Seen) (j : State) : ℤ :=
  scan pass none s fun c t => if classOf t (pairs c) = j then 1 else 0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem transition_counts (i : State) (j : State) :
    countTo (incoming (representative i)) (seen (stageOf i)) j = T i j := by
  revert i j
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem first_counts :
    ∀ j, countTo anchored (false, false, false) j = initial j := by
  decide +kernel

private theorem group_by_class (pass : Fin 5 → Fin 8 → Bool) (s : Seen)
    (v : State → ℤ) :
    scan pass none s (fun c t => v (classOf t (pairs c))) =
      ∑ j, countTo pass s j * v j := by
  simp only [countTo, scan_eq]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with h
  · simp
  · simp

private def power (n : ℕ) : State → ℤ := (T ^ n).mulVec 1

private theorem continuation_eq (n : ℕ) (s : Seen) (p : Boundary)
    (hs : coherent s) (hp : proper p) (hb : bounded (stage s) p) :
    continuation n s p = power n (classOf s p) := by
  induction n generalizing s p with
  | zero => simp [widthV, power, Matrix.one_mulVec]
  | succ n ih =>
    let i := classOf s p
    obtain ⟨hπ, hfix, hstage, hrep⟩ := class_spec s p hs hp hb
    have hre : representative i = fun j => rename p (p j) := funext hrep
    have hse : seen (stageOf i) = s := (congrArg seen hstage).trans hs
    rw [← continuation_recolour (n + 1) (rename p) (stage s) hπ hfix s hs le_rfl p,
      ← hre]
    change (∑ c : Row, if rowLegal c ∧ compatible (representative i) c ∧ good s c then
      continuation n (finish s c) (pairs c) else 0) = _
    have hscan : scan (incoming (representative i)) none s
          (fun c t => power n (classOf t (pairs c))) =
        ∑ c : Row, if rowLegal c ∧ compatible (representative i) c ∧ good s c then
          continuation n (finish s c) (pairs c) else 0 := by
      rw [scan_eq]
      simp only [incoming_iff, pathOK_iff]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : rowLegal c ∧ compatible (representative i) c ∧ good s c
      · obtain ⟨hcoh, _, hbound⟩ := row_valid s c hs hc.2.2
        rw [ite_eq_left ⟨hc.2.1, hc.1, hc.2.2⟩, ite_eq_left hc,
          ih _ _ hcoh ((row_iff c).mp hc.1) hbound]
      · rw [ite_eq_right (fun h => hc ⟨h.2.1, h.1, h.2.2⟩), ite_eq_right hc]
    rw [← hscan]
    conv_lhs => rw [← hse]
    rw [group_by_class]
    simp_rw [transition_counts]
    change (T.mulVec (power n)) i = power (n + 1) i
    rw [power, power, pow_succ', ← Matrix.mulVec_mulVec]

private theorem a_eq_power (n : ℕ) :
    (a (n + 1) : ℤ) = dotProduct initial (power n) := by
  rw [counting_bridge, widthTotal]
  have hscan : scan anchored none (false, false, false)
        (fun c t => power n (classOf t (pairs c))) =
      ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c then
        continuation n (finish (false, false, false) c) (pairs c) else 0 := by
    rw [scan_eq]
    simp only [anchored_iff, pathOK_iff]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs with hc
    · obtain ⟨hcoh, _, hb⟩ := row_valid (false, false, false) c (by decide) hc.2.2
      exact (continuation_eq n _ _ hcoh ((row_iff c).mp hc.2.1) hb).symm
    · rfl
  rw [← hscan, group_by_class]
  simp only [first_counts, dotProduct]

/-- All ten signed lags of OEIS A233199, for each source height at least twelve. -/
theorem result (n : ℕ) (hn : 12 ≤ n) :
    (a n : ℤ) = 736 * a (n - 1) - 203776 * a (n - 2) + 33062912 * a (n - 3)
      - 3665821696 * a (n - 4) + 270851375104 * a (n - 5) - 10685878632448 * a (n - 6)
      - 116548232544256 * a (n - 7) + 35184372088832000 * a (n - 8)
      - 1423137482249076736 * a (n - 9) + 18446744073709551616 * a (n - 10) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 12 := ⟨n - 12, by omega⟩
  have h := TransferMatrix.scalarRelationShift T initial 10 1 coeff vector_relation k
  rw [show k + 1 + 10 = k + 11 by omega] at h
  change dotProduct initial (power (k + 11)) =
    ∑ j : Fin 10, coeff j * dotProduct initial (power (k + 1 + j.val)) at h
  simp_rw [← a_eq_power] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    coeff] at h
  norm_num [Nat.add_assoc] at h
  rw [show k + 12 - 1 = k + 11 by omega,
    show k + 12 - 2 = k + 10 by omega,
    show k + 12 - 3 = k + 9 by omega,
    show k + 12 - 4 = k + 8 by omega,
    show k + 12 - 5 = k + 7 by omega,
    show k + 12 - 6 = k + 6 by omega,
    show k + 12 - 7 = k + 5 by omega,
    show k + 12 - 8 = k + 4 by omega,
    show k + 12 - 9 = k + 3 by omega,
    show k + 12 - 10 = k + 2 by omega]
  linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence
