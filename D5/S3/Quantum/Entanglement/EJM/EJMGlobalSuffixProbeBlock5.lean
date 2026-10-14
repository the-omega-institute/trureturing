/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock5
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock5
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: Exact full subtree leaf receipts and every four-child split are assembled without changing their actual contexts. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1804 : Cache :=
  step cache1803 ⟨16, by decide⟩ 0
private def partial1804 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1803 ⟨16, by decide⟩ (some 0)

private def cache1805 : Cache :=
  step cache1803 ⟨16, by decide⟩ 1
private def partial1805 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1803 ⟨16, by decide⟩ (some 1)

private def cache1806 : Cache :=
  step cache1803 ⟨16, by decide⟩ 2
private def partial1806 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1803 ⟨16, by decide⟩ (some 2)

private def cache1807 : Cache :=
  step cache1803 ⟨16, by decide⟩ 3
private def partial1807 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1803 ⟨16, by decide⟩ (some 3)

private def cache1808 : Cache :=
  step cache1807 ⟨17, by decide⟩ 0
private def partial1808 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1807 ⟨17, by decide⟩ (some 0)

private def cache1809 : Cache :=
  step cache1807 ⟨17, by decide⟩ 1
private def partial1809 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1807 ⟨17, by decide⟩ (some 1)

private def cache1810 : Cache :=
  step cache1809 ⟨18, by decide⟩ 0
private def partial1810 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1809 ⟨18, by decide⟩ (some 0)

private def cache1811 : Cache :=
  step cache1809 ⟨18, by decide⟩ 1
private def partial1811 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1809 ⟨18, by decide⟩ (some 1)

private def cache1812 : Cache :=
  step cache1811 ⟨19, by decide⟩ 0
private def partial1812 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1811 ⟨19, by decide⟩ (some 0)

private def cache1813 : Cache :=
  step cache1811 ⟨19, by decide⟩ 1
private def partial1813 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1811 ⟨19, by decide⟩ (some 1)

private def cache1814 : Cache :=
  step cache1811 ⟨19, by decide⟩ 2
private def partial1814 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1811 ⟨19, by decide⟩ (some 2)

private def cache1815 : Cache :=
  step cache1811 ⟨19, by decide⟩ 3
private def partial1815 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1811 ⟨19, by decide⟩ (some 3)

private def cache1816 : Cache :=
  step cache1809 ⟨18, by decide⟩ 2
private def partial1816 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1809 ⟨18, by decide⟩ (some 2)

private def cache1817 : Cache :=
  step cache1809 ⟨18, by decide⟩ 3
private def partial1817 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1809 ⟨18, by decide⟩ (some 3)

private def cache1818 : Cache :=
  step cache1817 ⟨19, by decide⟩ 0
private def partial1818 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1817 ⟨19, by decide⟩ (some 0)

private def cache1819 : Cache :=
  step cache1817 ⟨19, by decide⟩ 1
private def partial1819 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1817 ⟨19, by decide⟩ (some 1)

private def cache1820 : Cache :=
  step cache1817 ⟨19, by decide⟩ 2
private def partial1820 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1817 ⟨19, by decide⟩ (some 2)

private def cache1821 : Cache :=
  step cache1817 ⟨19, by decide⟩ 3
private def partial1821 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1817 ⟨19, by decide⟩ (some 3)

private def cache1822 : Cache :=
  step cache1807 ⟨17, by decide⟩ 2
private def partial1822 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1807 ⟨17, by decide⟩ (some 2)

private def cache1823 : Cache :=
  step cache1822 ⟨18, by decide⟩ 0
private def partial1823 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1822 ⟨18, by decide⟩ (some 0)

private def cache1824 : Cache :=
  step cache1823 ⟨19, by decide⟩ 0
private def partial1824 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1823 ⟨19, by decide⟩ (some 0)

private def cache1825 : Cache :=
  step cache1823 ⟨19, by decide⟩ 1
private def partial1825 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1823 ⟨19, by decide⟩ (some 1)

private def cache1826 : Cache :=
  step cache1823 ⟨19, by decide⟩ 2
private def partial1826 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1823 ⟨19, by decide⟩ (some 2)

private def cache1827 : Cache :=
  step cache1823 ⟨19, by decide⟩ 3
private def partial1827 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1823 ⟨19, by decide⟩ (some 3)

private def cache1828 : Cache :=
  step cache1822 ⟨18, by decide⟩ 1
private def partial1828 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1822 ⟨18, by decide⟩ (some 1)

private def cache1829 : Cache :=
  step cache1828 ⟨19, by decide⟩ 0
private def partial1829 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1828 ⟨19, by decide⟩ (some 0)

private def cache1830 : Cache :=
  step cache1828 ⟨19, by decide⟩ 1
private def partial1830 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1828 ⟨19, by decide⟩ (some 1)

private def cache1831 : Cache :=
  step cache1828 ⟨19, by decide⟩ 2
private def partial1831 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1828 ⟨19, by decide⟩ (some 2)

private def cache1832 : Cache :=
  step cache1828 ⟨19, by decide⟩ 3
private def partial1832 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1828 ⟨19, by decide⟩ (some 3)

private def cache1833 : Cache :=
  step cache1822 ⟨18, by decide⟩ 2
private def partial1833 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1822 ⟨18, by decide⟩ (some 2)

private def cache1834 : Cache :=
  step cache1833 ⟨19, by decide⟩ 0
private def partial1834 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1833 ⟨19, by decide⟩ (some 0)

private def cache1835 : Cache :=
  step cache1833 ⟨19, by decide⟩ 1
private def partial1835 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1833 ⟨19, by decide⟩ (some 1)

private def cache1836 : Cache :=
  step cache1833 ⟨19, by decide⟩ 2
private def partial1836 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1833 ⟨19, by decide⟩ (some 2)

private def cache1837 : Cache :=
  step cache1833 ⟨19, by decide⟩ 3
private def partial1837 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1833 ⟨19, by decide⟩ (some 3)

private def cache1838 : Cache :=
  step cache1822 ⟨18, by decide⟩ 3
private def partial1838 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1822 ⟨18, by decide⟩ (some 3)

private def cache1839 : Cache :=
  step cache1838 ⟨19, by decide⟩ 0
private def partial1839 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1838 ⟨19, by decide⟩ (some 0)

private def cache1840 : Cache :=
  step cache1838 ⟨19, by decide⟩ 1
private def partial1840 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1838 ⟨19, by decide⟩ (some 1)

private def cache1841 : Cache :=
  step cache1838 ⟨19, by decide⟩ 2
private def partial1841 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1838 ⟨19, by decide⟩ (some 2)

private def cache1842 : Cache :=
  step cache1838 ⟨19, by decide⟩ 3
private def partial1842 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1838 ⟨19, by decide⟩ (some 3)

private def cache1843 : Cache :=
  step cache1807 ⟨17, by decide⟩ 3
private def partial1843 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1807 ⟨17, by decide⟩ (some 3)

private def cache1844 : Cache :=
  step cache1843 ⟨18, by decide⟩ 0
private def partial1844 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1843 ⟨18, by decide⟩ (some 0)

private def cache1845 : Cache :=
  step cache1844 ⟨19, by decide⟩ 0
private def partial1845 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1844 ⟨19, by decide⟩ (some 0)

private def cache1846 : Cache :=
  step cache1844 ⟨19, by decide⟩ 1
private def partial1846 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1844 ⟨19, by decide⟩ (some 1)

private def cache1847 : Cache :=
  step cache1844 ⟨19, by decide⟩ 2
private def partial1847 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1844 ⟨19, by decide⟩ (some 2)

private def cache1848 : Cache :=
  step cache1844 ⟨19, by decide⟩ 3
private def partial1848 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1844 ⟨19, by decide⟩ (some 3)

private def cache1849 : Cache :=
  step cache1843 ⟨18, by decide⟩ 1
private def partial1849 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1843 ⟨18, by decide⟩ (some 1)

private def cache1850 : Cache :=
  step cache1849 ⟨19, by decide⟩ 0
private def partial1850 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1849 ⟨19, by decide⟩ (some 0)

private def cache1851 : Cache :=
  step cache1849 ⟨19, by decide⟩ 1
private def partial1851 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1849 ⟨19, by decide⟩ (some 1)

private def cache1852 : Cache :=
  step cache1849 ⟨19, by decide⟩ 2
private def partial1852 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1849 ⟨19, by decide⟩ (some 2)

private def cache1853 : Cache :=
  step cache1849 ⟨19, by decide⟩ 3
private def partial1853 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1849 ⟨19, by decide⟩ (some 3)

private def cache1854 : Cache :=
  step cache1843 ⟨18, by decide⟩ 2
private def partial1854 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1843 ⟨18, by decide⟩ (some 2)

private def cache1855 : Cache :=
  step cache1854 ⟨19, by decide⟩ 0
private def partial1855 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1854 ⟨19, by decide⟩ (some 0)

private def cache1856 : Cache :=
  step cache1854 ⟨19, by decide⟩ 1
private def partial1856 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1854 ⟨19, by decide⟩ (some 1)

private def cache1857 : Cache :=
  step cache1854 ⟨19, by decide⟩ 2
private def partial1857 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1854 ⟨19, by decide⟩ (some 2)

private def cache1858 : Cache :=
  step cache1854 ⟨19, by decide⟩ 3
private def partial1858 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1854 ⟨19, by decide⟩ (some 3)

private def cache1859 : Cache :=
  step cache1843 ⟨18, by decide⟩ 3
private def partial1859 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1843 ⟨18, by decide⟩ (some 3)

private def cache1860 : Cache :=
  step cache1859 ⟨19, by decide⟩ 0
private def partial1860 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1859 ⟨19, by decide⟩ (some 0)

private def cache1861 : Cache :=
  step cache1859 ⟨19, by decide⟩ 1
private def partial1861 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1859 ⟨19, by decide⟩ (some 1)

private def cache1862 : Cache :=
  step cache1859 ⟨19, by decide⟩ 2
private def partial1862 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1859 ⟨19, by decide⟩ (some 2)

private def cache1863 : Cache :=
  step cache1859 ⟨19, by decide⟩ 3
private def partial1863 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1859 ⟨19, by decide⟩ (some 3)

private theorem receipt1863 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1863, by decide⟩ cache1863 partial1863 = true := by
  decide +kernel

private theorem receipt1862 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1862, by decide⟩ cache1862 partial1862 = true := by
  decide +kernel

private theorem receipt1861 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1861, by decide⟩ cache1861 partial1861 = true := by
  decide +kernel

private theorem receipt1860 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1860, by decide⟩ cache1860 partial1860 = true := by
  decide +kernel

private theorem receipt1859 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1859, by decide⟩ cache1859 partial1859 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1860,1861,1862,1863])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4097780222716051 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1860
  · exact receipt1861
  · exact receipt1862
  · exact receipt1863

private theorem receipt1858 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1858, by decide⟩ cache1858 partial1858 = true := by
  decide +kernel

private theorem receipt1857 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1857, by decide⟩ cache1857 partial1857 = true := by
  decide +kernel

private theorem receipt1856 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1856, by decide⟩ cache1856 partial1856 = true := by
  decide +kernel

private theorem receipt1855 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1855, by decide⟩ cache1855 partial1855 = true := by
  decide +kernel

private theorem receipt1854 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1854, by decide⟩ cache1854 partial1854 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1855,1856,1857,1858])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4086782421428211 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1855
  · exact receipt1856
  · exact receipt1857
  · exact receipt1858

private theorem receipt1853 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1853, by decide⟩ cache1853 partial1853 = true := by
  decide +kernel

private theorem receipt1852 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1852, by decide⟩ cache1852 partial1852 = true := by
  decide +kernel

private theorem receipt1851 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1851, by decide⟩ cache1851 partial1851 = true := by
  decide +kernel

private theorem receipt1850 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1850, by decide⟩ cache1850 partial1850 = true := by
  decide +kernel

private theorem receipt1849 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1849, by decide⟩ cache1849 partial1849 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1850,1851,1852,1853])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4075784620140371 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1850
  · exact receipt1851
  · exact receipt1852
  · exact receipt1853

private theorem receipt1848 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1848, by decide⟩ cache1848 partial1848 = true := by
  decide +kernel

private theorem receipt1847 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1847, by decide⟩ cache1847 partial1847 = true := by
  decide +kernel

private theorem receipt1846 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1846, by decide⟩ cache1846 partial1846 = true := by
  decide +kernel

private theorem receipt1845 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1845, by decide⟩ cache1845 partial1845 = true := by
  decide +kernel

private theorem receipt1844 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1844, by decide⟩ cache1844 partial1844 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1845,1846,1847,1848])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4064786818852531 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1845
  · exact receipt1846
  · exact receipt1847
  · exact receipt1848

private theorem receipt1843 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1843, by decide⟩ cache1843 partial1843 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1844,1849,1854,1859])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4088979833153170 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1844
  · exact receipt1849
  · exact receipt1854
  · exact receipt1859

private theorem receipt1842 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1842, by decide⟩ cache1842 partial1842 = true := by
  decide +kernel

private theorem receipt1841 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1841, by decide⟩ cache1841 partial1841 = true := by
  decide +kernel

private theorem receipt1840 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1840, by decide⟩ cache1840 partial1840 = true := by
  decide +kernel

private theorem receipt1839 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1839, by decide⟩ cache1839 partial1839 = true := by
  decide +kernel

private theorem receipt1838 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1838, by decide⟩ cache1838 partial1838 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1839,1840,1841,1842])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4051589457307123 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1839
  · exact receipt1840
  · exact receipt1841
  · exact receipt1842

private theorem receipt1837 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1837, by decide⟩ cache1837 partial1837 = true := by
  decide +kernel

private theorem receipt1836 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1836, by decide⟩ cache1836 partial1836 = true := by
  decide +kernel

private theorem receipt1835 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1835, by decide⟩ cache1835 partial1835 = true := by
  decide +kernel

private theorem receipt1834 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1834, by decide⟩ cache1834 partial1834 = true := by
  decide +kernel

private theorem receipt1833 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1833, by decide⟩ cache1833 partial1833 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1834,1835,1836,1837])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4040591656019283 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1834
  · exact receipt1835
  · exact receipt1836
  · exact receipt1837

private theorem receipt1832 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1832, by decide⟩ cache1832 partial1832 = true := by
  decide +kernel

private theorem receipt1831 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1831, by decide⟩ cache1831 partial1831 = true := by
  decide +kernel

private theorem receipt1830 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1830, by decide⟩ cache1830 partial1830 = true := by
  decide +kernel

private theorem receipt1829 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1829, by decide⟩ cache1829 partial1829 = true := by
  decide +kernel

private theorem receipt1828 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1828, by decide⟩ cache1828 partial1828 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1829,1830,1831,1832])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4029593854731443 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1829
  · exact receipt1830
  · exact receipt1831
  · exact receipt1832

private theorem receipt1827 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1827, by decide⟩ cache1827 partial1827 = true := by
  decide +kernel

private theorem receipt1826 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1826, by decide⟩ cache1826 partial1826 = true := by
  decide +kernel

private theorem receipt1825 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1825, by decide⟩ cache1825 partial1825 = true := by
  decide +kernel

private theorem receipt1824 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1824, by decide⟩ cache1824 partial1824 = true := by
  decide +kernel

private theorem receipt1823 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1823, by decide⟩ cache1823 partial1823 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1824,1825,1826,1827])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4018596053443603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1824
  · exact receipt1825
  · exact receipt1826
  · exact receipt1827

private theorem receipt1822 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1822, by decide⟩ cache1822 partial1822 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1823,1828,1833,1838])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4042789067744242 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1823
  · exact receipt1828
  · exact receipt1833
  · exact receipt1838

private theorem receipt1821 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1821, by decide⟩ cache1821 partial1821 = true := by
  decide +kernel

private theorem receipt1820 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1820, by decide⟩ cache1820 partial1820 = true := by
  decide +kernel

private theorem receipt1819 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1819, by decide⟩ cache1819 partial1819 = true := by
  decide +kernel

private theorem receipt1818 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1818, by decide⟩ cache1818 partial1818 = true := by
  decide +kernel

private theorem receipt1817 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1817, by decide⟩ cache1817 partial1817 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1818,1819,1820,1821])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4005398691898195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1818
  · exact receipt1819
  · exact receipt1820
  · exact receipt1821

private theorem receipt1816 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1816, by decide⟩ cache1816 partial1816 = true := by
  decide +kernel

private theorem receipt1815 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1815, by decide⟩ cache1815 partial1815 = true := by
  decide +kernel

private theorem receipt1814 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1814, by decide⟩ cache1814 partial1814 = true := by
  decide +kernel

private theorem receipt1813 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1813, by decide⟩ cache1813 partial1813 = true := by
  decide +kernel

private theorem receipt1812 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1812, by decide⟩ cache1812 partial1812 = true := by
  decide +kernel

private theorem receipt1811 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1811, by decide⟩ cache1811 partial1811 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1812,1813,1814,1815])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3992201330352787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1812
  · exact receipt1813
  · exact receipt1814
  · exact receipt1815

private theorem receipt1810 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1810, by decide⟩ cache1810 partial1810 = true := by
  decide +kernel

private theorem receipt1809 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1809, by decide⟩ cache1809 partial1809 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1810,1811,1816,1817])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3996600450343506 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1810
  · exact receipt1811
  · exact receipt1816
  · exact receipt1817

private theorem receipt1808 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1808, by decide⟩ cache1808 partial1808 = true := by
  decide +kernel

private theorem receipt1807 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1807, by decide⟩ cache1807 partial1807 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1808,1809,1822,1843])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4053778275951121 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1808
  · exact receipt1809
  · exact receipt1822
  · exact receipt1843

private theorem receipt1806 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1806, by decide⟩ cache1806 partial1806 = true := by
  decide +kernel

private theorem receipt1805 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1805, by decide⟩ cache1805 partial1805 = true := by
  decide +kernel

private theorem receipt1804 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1804, by decide⟩ cache1804 partial1804 = true := by
  decide +kernel

theorem receipt1803 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1803, by decide⟩ cache1803 partial1803 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1804,1805,1806,1807])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3974604848292240 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1804
  · exact receipt1805
  · exact receipt1806
  · exact receipt1807


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock5
