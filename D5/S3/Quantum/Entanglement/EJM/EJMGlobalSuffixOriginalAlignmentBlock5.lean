/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock5
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock5
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock9
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock5
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1803 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1803 ∧ right = 161503) ∨
  (fuel = 4 ∧ left = 1804 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 1805 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 1806 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 1807 ∧ right = 161434) ∨
  (fuel = 3 ∧ left = 1808 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1809 ∧ right = 113677) ∨
  (fuel = 2 ∧ left = 1810 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1811 ∧ right = 92212) ∨
  (fuel = 1 ∧ left = 1812 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1813 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1814 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1815 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1816 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1817 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1818 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1819 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1820 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1821 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1822 ∧ right = 108651) ∨
  (fuel = 2 ∧ left = 1823 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 1824 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1825 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 1826 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1827 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1828 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1829 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1830 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1831 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1832 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1833 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1834 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1835 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1836 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1837 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1838 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1839 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1840 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1841 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1842 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1843 ∧ right = 108651) ∨
  (fuel = 2 ∧ left = 1844 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 1845 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1846 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 1847 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1848 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1849 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1850 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1851 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1852 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1853 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1854 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1855 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1856 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1857 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1858 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1859 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 1860 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1861 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1862 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1863 ∧ right = 0)

private theorem alignment1803 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1803 (fuel + 1) left right) :
    StepRelated (Related1803 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 1803 = .split (16 : Fin 20) ![1804,1805,1806,1807] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3974604848292240 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock9.shape_5_161503]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related1803 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related1803 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related1803 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1807 = .split (17 : Fin 20) ![1808,1809,1822,1843] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4053778275951121 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_4_161434]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1803 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1809 = .split (18 : Fin 20) ![1810,1811,1816,1817] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3996600450343506 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113677]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1803 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1811 = .split (19 : Fin 20) ![1812,1813,1814,1815] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3992201330352787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92212]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1803 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1817 = .split (19 : Fin 20) ![1818,1819,1820,1821] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4005398691898195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1822 = .split (18 : Fin 20) ![1823,1828,1833,1838] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4042789067744242 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_108651]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1823 = .split (19 : Fin 20) ![1824,1825,1826,1827] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4018596053443603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1828 = .split (19 : Fin 20) ![1829,1830,1831,1832] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4029593854731443 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1833 = .split (19 : Fin 20) ![1834,1835,1836,1837] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4040591656019283 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1838 = .split (19 : Fin 20) ![1839,1840,1841,1842] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4051589457307123 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1843 = .split (18 : Fin 20) ![1844,1849,1854,1859] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4088979833153170 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_108651]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1844 = .split (19 : Fin 20) ![1845,1846,1847,1848] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4064786818852531 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1849 = .split (19 : Fin 20) ![1850,1851,1852,1853] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4075784620140371 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1854 = .split (19 : Fin 20) ![1855,1856,1857,1858] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4086782421428211 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1859 = .split (19 : Fin 20) ![1860,1861,1862,1863] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4097780222716051 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1803 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1803 0) .bound .bound
    exact .bound

theorem originalReceipt1803 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 161503 cache1803 partial1803 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1803 alignment1803
    5 1803 161503 cache1803 partial1803 (by unfold Related1803; decide +kernel)
    EJMGlobalSuffixProbeBlock5.receipt1803

#print axioms originalReceipt1803

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock5
