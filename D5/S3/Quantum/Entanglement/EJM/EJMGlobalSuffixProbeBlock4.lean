/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock4
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock4
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock4
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1865 : Cache :=
  step cache1864 ⟨16, by decide⟩ 0
private def partial1865 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1864 ⟨16, by decide⟩ (some 0)

private def cache1866 : Cache :=
  step cache1864 ⟨16, by decide⟩ 1
private def partial1866 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1864 ⟨16, by decide⟩ (some 1)

private def cache1867 : Cache :=
  step cache1864 ⟨16, by decide⟩ 2
private def partial1867 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1864 ⟨16, by decide⟩ (some 2)

private def cache1868 : Cache :=
  step cache1864 ⟨16, by decide⟩ 3
private def partial1868 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1864 ⟨16, by decide⟩ (some 3)

private def cache1869 : Cache :=
  step cache1868 ⟨17, by decide⟩ 0
private def partial1869 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1868 ⟨17, by decide⟩ (some 0)

private def cache1870 : Cache :=
  step cache1868 ⟨17, by decide⟩ 1
private def partial1870 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1868 ⟨17, by decide⟩ (some 1)

private def cache1871 : Cache :=
  step cache1870 ⟨18, by decide⟩ 0
private def partial1871 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1870 ⟨18, by decide⟩ (some 0)

private def cache1872 : Cache :=
  step cache1870 ⟨18, by decide⟩ 1
private def partial1872 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1870 ⟨18, by decide⟩ (some 1)

private def cache1873 : Cache :=
  step cache1872 ⟨19, by decide⟩ 0
private def partial1873 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1872 ⟨19, by decide⟩ (some 0)

private def cache1874 : Cache :=
  step cache1872 ⟨19, by decide⟩ 1
private def partial1874 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1872 ⟨19, by decide⟩ (some 1)

private def cache1875 : Cache :=
  step cache1872 ⟨19, by decide⟩ 2
private def partial1875 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1872 ⟨19, by decide⟩ (some 2)

private def cache1876 : Cache :=
  step cache1872 ⟨19, by decide⟩ 3
private def partial1876 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1872 ⟨19, by decide⟩ (some 3)

private def cache1877 : Cache :=
  step cache1870 ⟨18, by decide⟩ 2
private def partial1877 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1870 ⟨18, by decide⟩ (some 2)

private def cache1878 : Cache :=
  step cache1877 ⟨19, by decide⟩ 0
private def partial1878 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1877 ⟨19, by decide⟩ (some 0)

private def cache1879 : Cache :=
  step cache1877 ⟨19, by decide⟩ 1
private def partial1879 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1877 ⟨19, by decide⟩ (some 1)

private def cache1880 : Cache :=
  step cache1877 ⟨19, by decide⟩ 2
private def partial1880 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1877 ⟨19, by decide⟩ (some 2)

private def cache1881 : Cache :=
  step cache1877 ⟨19, by decide⟩ 3
private def partial1881 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1877 ⟨19, by decide⟩ (some 3)

private def cache1882 : Cache :=
  step cache1870 ⟨18, by decide⟩ 3
private def partial1882 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1870 ⟨18, by decide⟩ (some 3)

private def cache1883 : Cache :=
  step cache1868 ⟨17, by decide⟩ 2
private def partial1883 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1868 ⟨17, by decide⟩ (some 2)

private def cache1884 : Cache :=
  step cache1883 ⟨18, by decide⟩ 0
private def partial1884 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1883 ⟨18, by decide⟩ (some 0)

private def cache1885 : Cache :=
  step cache1883 ⟨18, by decide⟩ 1
private def partial1885 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1883 ⟨18, by decide⟩ (some 1)

private def cache1886 : Cache :=
  step cache1885 ⟨19, by decide⟩ 0
private def partial1886 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1885 ⟨19, by decide⟩ (some 0)

private def cache1887 : Cache :=
  step cache1885 ⟨19, by decide⟩ 1
private def partial1887 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1885 ⟨19, by decide⟩ (some 1)

private def cache1888 : Cache :=
  step cache1885 ⟨19, by decide⟩ 2
private def partial1888 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1885 ⟨19, by decide⟩ (some 2)

private def cache1889 : Cache :=
  step cache1885 ⟨19, by decide⟩ 3
private def partial1889 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1885 ⟨19, by decide⟩ (some 3)

private def cache1890 : Cache :=
  step cache1883 ⟨18, by decide⟩ 2
private def partial1890 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1883 ⟨18, by decide⟩ (some 2)

private def cache1891 : Cache :=
  step cache1883 ⟨18, by decide⟩ 3
private def partial1891 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1883 ⟨18, by decide⟩ (some 3)

private def cache1892 : Cache :=
  step cache1868 ⟨17, by decide⟩ 3
private def partial1892 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1868 ⟨17, by decide⟩ (some 3)

private def cache1893 : Cache :=
  step cache1892 ⟨18, by decide⟩ 0
private def partial1893 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1892 ⟨18, by decide⟩ (some 0)

private def cache1894 : Cache :=
  step cache1893 ⟨19, by decide⟩ 0
private def partial1894 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1893 ⟨19, by decide⟩ (some 0)

private def cache1895 : Cache :=
  step cache1893 ⟨19, by decide⟩ 1
private def partial1895 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1893 ⟨19, by decide⟩ (some 1)

private def cache1896 : Cache :=
  step cache1893 ⟨19, by decide⟩ 2
private def partial1896 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1893 ⟨19, by decide⟩ (some 2)

private def cache1897 : Cache :=
  step cache1893 ⟨19, by decide⟩ 3
private def partial1897 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1893 ⟨19, by decide⟩ (some 3)

private def cache1898 : Cache :=
  step cache1892 ⟨18, by decide⟩ 1
private def partial1898 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1892 ⟨18, by decide⟩ (some 1)

private def cache1899 : Cache :=
  step cache1898 ⟨19, by decide⟩ 0
private def partial1899 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1898 ⟨19, by decide⟩ (some 0)

private def cache1900 : Cache :=
  step cache1898 ⟨19, by decide⟩ 1
private def partial1900 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1898 ⟨19, by decide⟩ (some 1)

private def cache1901 : Cache :=
  step cache1898 ⟨19, by decide⟩ 2
private def partial1901 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1898 ⟨19, by decide⟩ (some 2)

private def cache1902 : Cache :=
  step cache1898 ⟨19, by decide⟩ 3
private def partial1902 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1898 ⟨19, by decide⟩ (some 3)

private def cache1903 : Cache :=
  step cache1892 ⟨18, by decide⟩ 2
private def partial1903 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1892 ⟨18, by decide⟩ (some 2)

private def cache1904 : Cache :=
  step cache1903 ⟨19, by decide⟩ 0
private def partial1904 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1903 ⟨19, by decide⟩ (some 0)

private def cache1905 : Cache :=
  step cache1903 ⟨19, by decide⟩ 1
private def partial1905 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1903 ⟨19, by decide⟩ (some 1)

private def cache1906 : Cache :=
  step cache1903 ⟨19, by decide⟩ 2
private def partial1906 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1903 ⟨19, by decide⟩ (some 2)

private def cache1907 : Cache :=
  step cache1903 ⟨19, by decide⟩ 3
private def partial1907 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1903 ⟨19, by decide⟩ (some 3)

private def cache1908 : Cache :=
  step cache1892 ⟨18, by decide⟩ 3
private def partial1908 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1892 ⟨18, by decide⟩ (some 3)

private theorem receipt1908 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1908, by decide⟩ cache1908 partial1908 = true := by
  decide +kernel

private theorem receipt1907 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1907, by decide⟩ cache1907 partial1907 = true := by
  decide +kernel

private theorem receipt1906 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1906, by decide⟩ cache1906 partial1906 = true := by
  decide +kernel

private theorem receipt1905 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1905, by decide⟩ cache1905 partial1905 = true := by
  decide +kernel

private theorem receipt1904 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1904, by decide⟩ cache1904 partial1904 = true := by
  decide +kernel

private theorem receipt1903 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1903, by decide⟩ cache1903 partial1903 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1904,1905,1906,1907])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4194560874049043 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1904
  · exact receipt1905
  · exact receipt1906
  · exact receipt1907

private theorem receipt1902 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1902, by decide⟩ cache1902 partial1902 = true := by
  decide +kernel

private theorem receipt1901 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1901, by decide⟩ cache1901 partial1901 = true := by
  decide +kernel

private theorem receipt1900 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1900, by decide⟩ cache1900 partial1900 = true := by
  decide +kernel

private theorem receipt1899 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1899, by decide⟩ cache1899 partial1899 = true := by
  decide +kernel

private theorem receipt1898 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1898, by decide⟩ cache1898 partial1898 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1899,1900,1901,1902])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4183563072761203 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1899
  · exact receipt1900
  · exact receipt1901
  · exact receipt1902

private theorem receipt1897 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1897, by decide⟩ cache1897 partial1897 = true := by
  decide +kernel

private theorem receipt1896 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1896, by decide⟩ cache1896 partial1896 = true := by
  decide +kernel

private theorem receipt1895 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1895, by decide⟩ cache1895 partial1895 = true := by
  decide +kernel

private theorem receipt1894 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1894, by decide⟩ cache1894 partial1894 = true := by
  decide +kernel

private theorem receipt1893 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1893, by decide⟩ cache1893 partial1893 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1894,1895,1896,1897])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4172565271473363 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1894
  · exact receipt1895
  · exact receipt1896
  · exact receipt1897

private theorem receipt1892 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1892, by decide⟩ cache1892 partial1892 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1893,1898,1903,1908])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4196758285774002 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1893
  · exact receipt1898
  · exact receipt1903
  · exact receipt1908

private theorem receipt1891 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1891, by decide⟩ cache1891 partial1891 = true := by
  decide +kernel

private theorem receipt1890 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1890, by decide⟩ cache1890 partial1890 = true := by
  decide +kernel

private theorem receipt1889 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1889, by decide⟩ cache1889 partial1889 = true := by
  decide +kernel

private theorem receipt1888 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1888, by decide⟩ cache1888 partial1888 = true := by
  decide +kernel

private theorem receipt1887 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1887, by decide⟩ cache1887 partial1887 = true := by
  decide +kernel

private theorem receipt1886 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1886, by decide⟩ cache1886 partial1886 = true := by
  decide +kernel

private theorem receipt1885 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1885, by decide⟩ cache1885 partial1885 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1886,1887,1888,1889])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4154968789412819 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1886
  · exact receipt1887
  · exact receipt1888
  · exact receipt1889

private theorem receipt1884 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1884, by decide⟩ cache1884 partial1884 = true := by
  decide +kernel

private theorem receipt1883 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1883, by decide⟩ cache1883 partial1883 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1884,1885,1890,1891])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4159367909403538 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1884
  · exact receipt1885
  · exact receipt1890
  · exact receipt1891

private theorem receipt1882 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1882, by decide⟩ cache1882 partial1882 = true := by
  decide +kernel

private theorem receipt1881 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1881, by decide⟩ cache1881 partial1881 = true := by
  decide +kernel

private theorem receipt1880 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1880, by decide⟩ cache1880 partial1880 = true := by
  decide +kernel

private theorem receipt1879 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1879, by decide⟩ cache1879 partial1879 = true := by
  decide +kernel

private theorem receipt1878 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1878, by decide⟩ cache1878 partial1878 = true := by
  decide +kernel

private theorem receipt1877 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1877, by decide⟩ cache1877 partial1877 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1878,1879,1880,1881])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4137372307352275 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1878
  · exact receipt1879
  · exact receipt1880
  · exact receipt1881

private theorem receipt1876 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1876, by decide⟩ cache1876 partial1876 = true := by
  decide +kernel

private theorem receipt1875 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1875, by decide⟩ cache1875 partial1875 = true := by
  decide +kernel

private theorem receipt1874 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1874, by decide⟩ cache1874 partial1874 = true := by
  decide +kernel

private theorem receipt1873 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1873, by decide⟩ cache1873 partial1873 = true := by
  decide +kernel

private theorem receipt1872 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1872, by decide⟩ cache1872 partial1872 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1873,1874,1875,1876])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4126374506064435 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1873
  · exact receipt1874
  · exact receipt1875
  · exact receipt1876

private theorem receipt1871 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1871, by decide⟩ cache1871 partial1871 = true := by
  decide +kernel

private theorem receipt1870 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1870, by decide⟩ cache1870 partial1870 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1871,1872,1877,1882])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4139569719077362 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1871
  · exact receipt1872
  · exact receipt1877
  · exact receipt1882

private theorem receipt1869 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1869, by decide⟩ cache1869 partial1869 = true := by
  decide +kernel

private theorem receipt1868 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1868, by decide⟩ cache1868 partial1868 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1869,1870,1883,1892])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4161563172596145 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1869
  · exact receipt1870
  · exact receipt1883
  · exact receipt1892

private theorem receipt1867 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1867, by decide⟩ cache1867 partial1867 = true := by
  decide +kernel

private theorem receipt1866 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1866, by decide⟩ cache1866 partial1866 = true := by
  decide +kernel

private theorem receipt1865 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1865, by decide⟩ cache1865 partial1865 = true := by
  decide +kernel

theorem receipt1864 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1864, by decide⟩ cache1864 partial1864 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1865,1866,1867,1868])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4108778024003888 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1865
  · exact receipt1866
  · exact receipt1867
  · exact receipt1868


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock4
