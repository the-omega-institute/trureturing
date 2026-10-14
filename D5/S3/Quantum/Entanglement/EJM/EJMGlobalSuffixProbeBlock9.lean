/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock9
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock9
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock9
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache785 : Cache :=
  step cache784 ⟨17, by decide⟩ 0
private def partial785 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 0)

private def cache786 : Cache :=
  step cache784 ⟨17, by decide⟩ 1
private def partial786 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 1)

private def cache787 : Cache :=
  step cache786 ⟨18, by decide⟩ 0
private def partial787 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 0)

private def cache788 : Cache :=
  step cache786 ⟨18, by decide⟩ 1
private def partial788 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 1)

private def cache789 : Cache :=
  step cache786 ⟨18, by decide⟩ 2
private def partial789 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 2)

private def cache790 : Cache :=
  step cache786 ⟨18, by decide⟩ 3
private def partial790 : Partial (Fin 20) (Fin 4) :=
  Function.update partial786 ⟨18, by decide⟩ (some 3)

private def cache791 : Cache :=
  step cache790 ⟨19, by decide⟩ 0
private def partial791 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 0)

private def cache792 : Cache :=
  step cache790 ⟨19, by decide⟩ 1
private def partial792 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 1)

private def cache793 : Cache :=
  step cache790 ⟨19, by decide⟩ 2
private def partial793 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 2)

private def cache794 : Cache :=
  step cache790 ⟨19, by decide⟩ 3
private def partial794 : Partial (Fin 20) (Fin 4) :=
  Function.update partial790 ⟨19, by decide⟩ (some 3)

private def cache795 : Cache :=
  step cache784 ⟨17, by decide⟩ 2
private def partial795 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 2)

private def cache796 : Cache :=
  step cache795 ⟨18, by decide⟩ 0
private def partial796 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 0)

private def cache797 : Cache :=
  step cache795 ⟨18, by decide⟩ 1
private def partial797 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 1)

private def cache798 : Cache :=
  step cache795 ⟨18, by decide⟩ 2
private def partial798 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 2)

private def cache799 : Cache :=
  step cache795 ⟨18, by decide⟩ 3
private def partial799 : Partial (Fin 20) (Fin 4) :=
  Function.update partial795 ⟨18, by decide⟩ (some 3)

private def cache800 : Cache :=
  step cache784 ⟨17, by decide⟩ 3
private def partial800 : Partial (Fin 20) (Fin 4) :=
  Function.update partial784 ⟨17, by decide⟩ (some 3)

private def cache801 : Cache :=
  step cache800 ⟨18, by decide⟩ 0
private def partial801 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 0)

private def cache802 : Cache :=
  step cache801 ⟨19, by decide⟩ 0
private def partial802 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 0)

private def cache803 : Cache :=
  step cache801 ⟨19, by decide⟩ 1
private def partial803 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 1)

private def cache804 : Cache :=
  step cache801 ⟨19, by decide⟩ 2
private def partial804 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 2)

private def cache805 : Cache :=
  step cache801 ⟨19, by decide⟩ 3
private def partial805 : Partial (Fin 20) (Fin 4) :=
  Function.update partial801 ⟨19, by decide⟩ (some 3)

private def cache806 : Cache :=
  step cache800 ⟨18, by decide⟩ 1
private def partial806 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 1)

private def cache807 : Cache :=
  step cache806 ⟨19, by decide⟩ 0
private def partial807 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 0)

private def cache808 : Cache :=
  step cache806 ⟨19, by decide⟩ 1
private def partial808 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 1)

private def cache809 : Cache :=
  step cache806 ⟨19, by decide⟩ 2
private def partial809 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 2)

private def cache810 : Cache :=
  step cache806 ⟨19, by decide⟩ 3
private def partial810 : Partial (Fin 20) (Fin 4) :=
  Function.update partial806 ⟨19, by decide⟩ (some 3)

private def cache811 : Cache :=
  step cache800 ⟨18, by decide⟩ 2
private def partial811 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 2)

private def cache812 : Cache :=
  step cache811 ⟨19, by decide⟩ 0
private def partial812 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 0)

private def cache813 : Cache :=
  step cache811 ⟨19, by decide⟩ 1
private def partial813 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 1)

private def cache814 : Cache :=
  step cache811 ⟨19, by decide⟩ 2
private def partial814 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 2)

private def cache815 : Cache :=
  step cache811 ⟨19, by decide⟩ 3
private def partial815 : Partial (Fin 20) (Fin 4) :=
  Function.update partial811 ⟨19, by decide⟩ (some 3)

private def cache816 : Cache :=
  step cache800 ⟨18, by decide⟩ 3
private def partial816 : Partial (Fin 20) (Fin 4) :=
  Function.update partial800 ⟨18, by decide⟩ (some 3)

private def cache817 : Cache :=
  step cache816 ⟨19, by decide⟩ 0
private def partial817 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 0)

private def cache818 : Cache :=
  step cache816 ⟨19, by decide⟩ 1
private def partial818 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 1)

private def cache819 : Cache :=
  step cache816 ⟨19, by decide⟩ 2
private def partial819 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 2)

private def cache820 : Cache :=
  step cache816 ⟨19, by decide⟩ 3
private def partial820 : Partial (Fin 20) (Fin 4) :=
  Function.update partial816 ⟨19, by decide⟩ (some 3)

private def cache822 : Cache :=
  step cache821 ⟨17, by decide⟩ 0
private def partial822 : Partial (Fin 20) (Fin 4) :=
  Function.update partial821 ⟨17, by decide⟩ (some 0)

private def cache823 : Cache :=
  step cache821 ⟨17, by decide⟩ 1
private def partial823 : Partial (Fin 20) (Fin 4) :=
  Function.update partial821 ⟨17, by decide⟩ (some 1)

private def cache824 : Cache :=
  step cache823 ⟨18, by decide⟩ 0
private def partial824 : Partial (Fin 20) (Fin 4) :=
  Function.update partial823 ⟨18, by decide⟩ (some 0)

private def cache825 : Cache :=
  step cache823 ⟨18, by decide⟩ 1
private def partial825 : Partial (Fin 20) (Fin 4) :=
  Function.update partial823 ⟨18, by decide⟩ (some 1)

private def cache826 : Cache :=
  step cache825 ⟨19, by decide⟩ 0
private def partial826 : Partial (Fin 20) (Fin 4) :=
  Function.update partial825 ⟨19, by decide⟩ (some 0)

private def cache827 : Cache :=
  step cache825 ⟨19, by decide⟩ 1
private def partial827 : Partial (Fin 20) (Fin 4) :=
  Function.update partial825 ⟨19, by decide⟩ (some 1)

private def cache828 : Cache :=
  step cache825 ⟨19, by decide⟩ 2
private def partial828 : Partial (Fin 20) (Fin 4) :=
  Function.update partial825 ⟨19, by decide⟩ (some 2)

private def cache829 : Cache :=
  step cache825 ⟨19, by decide⟩ 3
private def partial829 : Partial (Fin 20) (Fin 4) :=
  Function.update partial825 ⟨19, by decide⟩ (some 3)

private def cache830 : Cache :=
  step cache823 ⟨18, by decide⟩ 2
private def partial830 : Partial (Fin 20) (Fin 4) :=
  Function.update partial823 ⟨18, by decide⟩ (some 2)

private def cache831 : Cache :=
  step cache830 ⟨19, by decide⟩ 0
private def partial831 : Partial (Fin 20) (Fin 4) :=
  Function.update partial830 ⟨19, by decide⟩ (some 0)

private def cache832 : Cache :=
  step cache830 ⟨19, by decide⟩ 1
private def partial832 : Partial (Fin 20) (Fin 4) :=
  Function.update partial830 ⟨19, by decide⟩ (some 1)

private def cache833 : Cache :=
  step cache830 ⟨19, by decide⟩ 2
private def partial833 : Partial (Fin 20) (Fin 4) :=
  Function.update partial830 ⟨19, by decide⟩ (some 2)

private def cache834 : Cache :=
  step cache830 ⟨19, by decide⟩ 3
private def partial834 : Partial (Fin 20) (Fin 4) :=
  Function.update partial830 ⟨19, by decide⟩ (some 3)

private def cache835 : Cache :=
  step cache823 ⟨18, by decide⟩ 3
private def partial835 : Partial (Fin 20) (Fin 4) :=
  Function.update partial823 ⟨18, by decide⟩ (some 3)

private def cache836 : Cache :=
  step cache835 ⟨19, by decide⟩ 0
private def partial836 : Partial (Fin 20) (Fin 4) :=
  Function.update partial835 ⟨19, by decide⟩ (some 0)

private def cache837 : Cache :=
  step cache835 ⟨19, by decide⟩ 1
private def partial837 : Partial (Fin 20) (Fin 4) :=
  Function.update partial835 ⟨19, by decide⟩ (some 1)

private def cache838 : Cache :=
  step cache835 ⟨19, by decide⟩ 2
private def partial838 : Partial (Fin 20) (Fin 4) :=
  Function.update partial835 ⟨19, by decide⟩ (some 2)

private def cache839 : Cache :=
  step cache835 ⟨19, by decide⟩ 3
private def partial839 : Partial (Fin 20) (Fin 4) :=
  Function.update partial835 ⟨19, by decide⟩ (some 3)

private def cache840 : Cache :=
  step cache821 ⟨17, by decide⟩ 2
private def partial840 : Partial (Fin 20) (Fin 4) :=
  Function.update partial821 ⟨17, by decide⟩ (some 2)

private def cache841 : Cache :=
  step cache840 ⟨18, by decide⟩ 0
private def partial841 : Partial (Fin 20) (Fin 4) :=
  Function.update partial840 ⟨18, by decide⟩ (some 0)

private def cache842 : Cache :=
  step cache840 ⟨18, by decide⟩ 1
private def partial842 : Partial (Fin 20) (Fin 4) :=
  Function.update partial840 ⟨18, by decide⟩ (some 1)

private def cache843 : Cache :=
  step cache840 ⟨18, by decide⟩ 2
private def partial843 : Partial (Fin 20) (Fin 4) :=
  Function.update partial840 ⟨18, by decide⟩ (some 2)

private def cache844 : Cache :=
  step cache840 ⟨18, by decide⟩ 3
private def partial844 : Partial (Fin 20) (Fin 4) :=
  Function.update partial840 ⟨18, by decide⟩ (some 3)

private def cache845 : Cache :=
  step cache821 ⟨17, by decide⟩ 3
private def partial845 : Partial (Fin 20) (Fin 4) :=
  Function.update partial821 ⟨17, by decide⟩ (some 3)

private def cache846 : Cache :=
  step cache845 ⟨18, by decide⟩ 0
private def partial846 : Partial (Fin 20) (Fin 4) :=
  Function.update partial845 ⟨18, by decide⟩ (some 0)

private def cache847 : Cache :=
  step cache846 ⟨19, by decide⟩ 0
private def partial847 : Partial (Fin 20) (Fin 4) :=
  Function.update partial846 ⟨19, by decide⟩ (some 0)

private def cache848 : Cache :=
  step cache846 ⟨19, by decide⟩ 1
private def partial848 : Partial (Fin 20) (Fin 4) :=
  Function.update partial846 ⟨19, by decide⟩ (some 1)

private def cache849 : Cache :=
  step cache846 ⟨19, by decide⟩ 2
private def partial849 : Partial (Fin 20) (Fin 4) :=
  Function.update partial846 ⟨19, by decide⟩ (some 2)

private def cache850 : Cache :=
  step cache846 ⟨19, by decide⟩ 3
private def partial850 : Partial (Fin 20) (Fin 4) :=
  Function.update partial846 ⟨19, by decide⟩ (some 3)

private def cache851 : Cache :=
  step cache845 ⟨18, by decide⟩ 1
private def partial851 : Partial (Fin 20) (Fin 4) :=
  Function.update partial845 ⟨18, by decide⟩ (some 1)

private def cache852 : Cache :=
  step cache851 ⟨19, by decide⟩ 0
private def partial852 : Partial (Fin 20) (Fin 4) :=
  Function.update partial851 ⟨19, by decide⟩ (some 0)

private def cache853 : Cache :=
  step cache851 ⟨19, by decide⟩ 1
private def partial853 : Partial (Fin 20) (Fin 4) :=
  Function.update partial851 ⟨19, by decide⟩ (some 1)

private def cache854 : Cache :=
  step cache851 ⟨19, by decide⟩ 2
private def partial854 : Partial (Fin 20) (Fin 4) :=
  Function.update partial851 ⟨19, by decide⟩ (some 2)

private def cache855 : Cache :=
  step cache851 ⟨19, by decide⟩ 3
private def partial855 : Partial (Fin 20) (Fin 4) :=
  Function.update partial851 ⟨19, by decide⟩ (some 3)

private def cache856 : Cache :=
  step cache845 ⟨18, by decide⟩ 2
private def partial856 : Partial (Fin 20) (Fin 4) :=
  Function.update partial845 ⟨18, by decide⟩ (some 2)

private def cache857 : Cache :=
  step cache845 ⟨18, by decide⟩ 3
private def partial857 : Partial (Fin 20) (Fin 4) :=
  Function.update partial845 ⟨18, by decide⟩ (some 3)

private def cache866 : Cache :=
  step cache865 ⟨17, by decide⟩ 0
private def partial866 : Partial (Fin 20) (Fin 4) :=
  Function.update partial865 ⟨17, by decide⟩ (some 0)

private def cache867 : Cache :=
  step cache865 ⟨17, by decide⟩ 1
private def partial867 : Partial (Fin 20) (Fin 4) :=
  Function.update partial865 ⟨17, by decide⟩ (some 1)

private def cache868 : Cache :=
  step cache865 ⟨17, by decide⟩ 2
private def partial868 : Partial (Fin 20) (Fin 4) :=
  Function.update partial865 ⟨17, by decide⟩ (some 2)

private def cache869 : Cache :=
  step cache868 ⟨18, by decide⟩ 0
private def partial869 : Partial (Fin 20) (Fin 4) :=
  Function.update partial868 ⟨18, by decide⟩ (some 0)

private def cache870 : Cache :=
  step cache869 ⟨19, by decide⟩ 0
private def partial870 : Partial (Fin 20) (Fin 4) :=
  Function.update partial869 ⟨19, by decide⟩ (some 0)

private def cache871 : Cache :=
  step cache869 ⟨19, by decide⟩ 1
private def partial871 : Partial (Fin 20) (Fin 4) :=
  Function.update partial869 ⟨19, by decide⟩ (some 1)

private def cache872 : Cache :=
  step cache869 ⟨19, by decide⟩ 2
private def partial872 : Partial (Fin 20) (Fin 4) :=
  Function.update partial869 ⟨19, by decide⟩ (some 2)

private def cache873 : Cache :=
  step cache869 ⟨19, by decide⟩ 3
private def partial873 : Partial (Fin 20) (Fin 4) :=
  Function.update partial869 ⟨19, by decide⟩ (some 3)

private def cache874 : Cache :=
  step cache868 ⟨18, by decide⟩ 1
private def partial874 : Partial (Fin 20) (Fin 4) :=
  Function.update partial868 ⟨18, by decide⟩ (some 1)

private def cache875 : Cache :=
  step cache874 ⟨19, by decide⟩ 0
private def partial875 : Partial (Fin 20) (Fin 4) :=
  Function.update partial874 ⟨19, by decide⟩ (some 0)

private def cache876 : Cache :=
  step cache874 ⟨19, by decide⟩ 1
private def partial876 : Partial (Fin 20) (Fin 4) :=
  Function.update partial874 ⟨19, by decide⟩ (some 1)

private def cache877 : Cache :=
  step cache874 ⟨19, by decide⟩ 2
private def partial877 : Partial (Fin 20) (Fin 4) :=
  Function.update partial874 ⟨19, by decide⟩ (some 2)

private def cache878 : Cache :=
  step cache874 ⟨19, by decide⟩ 3
private def partial878 : Partial (Fin 20) (Fin 4) :=
  Function.update partial874 ⟨19, by decide⟩ (some 3)

private def cache879 : Cache :=
  step cache868 ⟨18, by decide⟩ 2
private def partial879 : Partial (Fin 20) (Fin 4) :=
  Function.update partial868 ⟨18, by decide⟩ (some 2)

private def cache880 : Cache :=
  step cache879 ⟨19, by decide⟩ 0
private def partial880 : Partial (Fin 20) (Fin 4) :=
  Function.update partial879 ⟨19, by decide⟩ (some 0)

private def cache881 : Cache :=
  step cache879 ⟨19, by decide⟩ 1
private def partial881 : Partial (Fin 20) (Fin 4) :=
  Function.update partial879 ⟨19, by decide⟩ (some 1)

private def cache882 : Cache :=
  step cache879 ⟨19, by decide⟩ 2
private def partial882 : Partial (Fin 20) (Fin 4) :=
  Function.update partial879 ⟨19, by decide⟩ (some 2)

private def cache883 : Cache :=
  step cache879 ⟨19, by decide⟩ 3
private def partial883 : Partial (Fin 20) (Fin 4) :=
  Function.update partial879 ⟨19, by decide⟩ (some 3)

private def cache884 : Cache :=
  step cache868 ⟨18, by decide⟩ 3
private def partial884 : Partial (Fin 20) (Fin 4) :=
  Function.update partial868 ⟨18, by decide⟩ (some 3)

private def cache885 : Cache :=
  step cache884 ⟨19, by decide⟩ 0
private def partial885 : Partial (Fin 20) (Fin 4) :=
  Function.update partial884 ⟨19, by decide⟩ (some 0)

private def cache886 : Cache :=
  step cache884 ⟨19, by decide⟩ 1
private def partial886 : Partial (Fin 20) (Fin 4) :=
  Function.update partial884 ⟨19, by decide⟩ (some 1)

private def cache887 : Cache :=
  step cache884 ⟨19, by decide⟩ 2
private def partial887 : Partial (Fin 20) (Fin 4) :=
  Function.update partial884 ⟨19, by decide⟩ (some 2)

private def cache888 : Cache :=
  step cache884 ⟨19, by decide⟩ 3
private def partial888 : Partial (Fin 20) (Fin 4) :=
  Function.update partial884 ⟨19, by decide⟩ (some 3)

private def cache889 : Cache :=
  step cache865 ⟨17, by decide⟩ 3
private def partial889 : Partial (Fin 20) (Fin 4) :=
  Function.update partial865 ⟨17, by decide⟩ (some 3)

private def cache890 : Cache :=
  step cache889 ⟨18, by decide⟩ 0
private def partial890 : Partial (Fin 20) (Fin 4) :=
  Function.update partial889 ⟨18, by decide⟩ (some 0)

private def cache891 : Cache :=
  step cache890 ⟨19, by decide⟩ 0
private def partial891 : Partial (Fin 20) (Fin 4) :=
  Function.update partial890 ⟨19, by decide⟩ (some 0)

private def cache892 : Cache :=
  step cache890 ⟨19, by decide⟩ 1
private def partial892 : Partial (Fin 20) (Fin 4) :=
  Function.update partial890 ⟨19, by decide⟩ (some 1)

private def cache893 : Cache :=
  step cache890 ⟨19, by decide⟩ 2
private def partial893 : Partial (Fin 20) (Fin 4) :=
  Function.update partial890 ⟨19, by decide⟩ (some 2)

private def cache894 : Cache :=
  step cache890 ⟨19, by decide⟩ 3
private def partial894 : Partial (Fin 20) (Fin 4) :=
  Function.update partial890 ⟨19, by decide⟩ (some 3)

private def cache895 : Cache :=
  step cache889 ⟨18, by decide⟩ 1
private def partial895 : Partial (Fin 20) (Fin 4) :=
  Function.update partial889 ⟨18, by decide⟩ (some 1)

private def cache896 : Cache :=
  step cache895 ⟨19, by decide⟩ 0
private def partial896 : Partial (Fin 20) (Fin 4) :=
  Function.update partial895 ⟨19, by decide⟩ (some 0)

private def cache897 : Cache :=
  step cache895 ⟨19, by decide⟩ 1
private def partial897 : Partial (Fin 20) (Fin 4) :=
  Function.update partial895 ⟨19, by decide⟩ (some 1)

private def cache898 : Cache :=
  step cache895 ⟨19, by decide⟩ 2
private def partial898 : Partial (Fin 20) (Fin 4) :=
  Function.update partial895 ⟨19, by decide⟩ (some 2)

private def cache899 : Cache :=
  step cache895 ⟨19, by decide⟩ 3
private def partial899 : Partial (Fin 20) (Fin 4) :=
  Function.update partial895 ⟨19, by decide⟩ (some 3)

private def cache900 : Cache :=
  step cache889 ⟨18, by decide⟩ 2
private def partial900 : Partial (Fin 20) (Fin 4) :=
  Function.update partial889 ⟨18, by decide⟩ (some 2)

private def cache901 : Cache :=
  step cache900 ⟨19, by decide⟩ 0
private def partial901 : Partial (Fin 20) (Fin 4) :=
  Function.update partial900 ⟨19, by decide⟩ (some 0)

private def cache902 : Cache :=
  step cache900 ⟨19, by decide⟩ 1
private def partial902 : Partial (Fin 20) (Fin 4) :=
  Function.update partial900 ⟨19, by decide⟩ (some 1)

private def cache903 : Cache :=
  step cache900 ⟨19, by decide⟩ 2
private def partial903 : Partial (Fin 20) (Fin 4) :=
  Function.update partial900 ⟨19, by decide⟩ (some 2)

private def cache904 : Cache :=
  step cache900 ⟨19, by decide⟩ 3
private def partial904 : Partial (Fin 20) (Fin 4) :=
  Function.update partial900 ⟨19, by decide⟩ (some 3)

private def cache905 : Cache :=
  step cache889 ⟨18, by decide⟩ 3
private def partial905 : Partial (Fin 20) (Fin 4) :=
  Function.update partial889 ⟨18, by decide⟩ (some 3)

private def cache907 : Cache :=
  step cache906 ⟨17, by decide⟩ 0
private def partial907 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 0)

private def cache908 : Cache :=
  step cache906 ⟨17, by decide⟩ 1
private def partial908 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 1)

private def cache909 : Cache :=
  step cache908 ⟨18, by decide⟩ 0
private def partial909 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 0)

private def cache910 : Cache :=
  step cache908 ⟨18, by decide⟩ 1
private def partial910 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 1)

private def cache911 : Cache :=
  step cache910 ⟨19, by decide⟩ 0
private def partial911 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 0)

private def cache912 : Cache :=
  step cache910 ⟨19, by decide⟩ 1
private def partial912 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 1)

private def cache913 : Cache :=
  step cache910 ⟨19, by decide⟩ 2
private def partial913 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 2)

private def cache914 : Cache :=
  step cache910 ⟨19, by decide⟩ 3
private def partial914 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 3)

private def cache915 : Cache :=
  step cache908 ⟨18, by decide⟩ 2
private def partial915 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 2)

private def cache916 : Cache :=
  step cache908 ⟨18, by decide⟩ 3
private def partial916 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 3)

private def cache917 : Cache :=
  step cache916 ⟨19, by decide⟩ 0
private def partial917 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 0)

private def cache918 : Cache :=
  step cache916 ⟨19, by decide⟩ 1
private def partial918 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 1)

private def cache919 : Cache :=
  step cache916 ⟨19, by decide⟩ 2
private def partial919 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 2)

private def cache920 : Cache :=
  step cache916 ⟨19, by decide⟩ 3
private def partial920 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 3)

private def cache921 : Cache :=
  step cache906 ⟨17, by decide⟩ 2
private def partial921 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 2)

private def cache922 : Cache :=
  step cache921 ⟨18, by decide⟩ 0
private def partial922 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 0)

private def cache923 : Cache :=
  step cache922 ⟨19, by decide⟩ 0
private def partial923 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 0)

private def cache924 : Cache :=
  step cache922 ⟨19, by decide⟩ 1
private def partial924 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 1)

private def cache925 : Cache :=
  step cache922 ⟨19, by decide⟩ 2
private def partial925 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 2)

private def cache926 : Cache :=
  step cache922 ⟨19, by decide⟩ 3
private def partial926 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 3)

private def cache927 : Cache :=
  step cache921 ⟨18, by decide⟩ 1
private def partial927 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 1)

private def cache928 : Cache :=
  step cache927 ⟨19, by decide⟩ 0
private def partial928 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 0)

private def cache929 : Cache :=
  step cache927 ⟨19, by decide⟩ 1
private def partial929 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 1)

private def cache930 : Cache :=
  step cache927 ⟨19, by decide⟩ 2
private def partial930 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 2)

private def cache931 : Cache :=
  step cache927 ⟨19, by decide⟩ 3
private def partial931 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 3)

private def cache932 : Cache :=
  step cache921 ⟨18, by decide⟩ 2
private def partial932 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 2)

private def cache933 : Cache :=
  step cache932 ⟨19, by decide⟩ 0
private def partial933 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 0)

private def cache934 : Cache :=
  step cache932 ⟨19, by decide⟩ 1
private def partial934 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 1)

private def cache935 : Cache :=
  step cache932 ⟨19, by decide⟩ 2
private def partial935 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 2)

private def cache936 : Cache :=
  step cache932 ⟨19, by decide⟩ 3
private def partial936 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 3)

private def cache937 : Cache :=
  step cache921 ⟨18, by decide⟩ 3
private def partial937 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 3)

private def cache938 : Cache :=
  step cache937 ⟨19, by decide⟩ 0
private def partial938 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 0)

private def cache939 : Cache :=
  step cache937 ⟨19, by decide⟩ 1
private def partial939 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 1)

private def cache940 : Cache :=
  step cache937 ⟨19, by decide⟩ 2
private def partial940 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 2)

private def cache941 : Cache :=
  step cache937 ⟨19, by decide⟩ 3
private def partial941 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 3)

private def cache942 : Cache :=
  step cache906 ⟨17, by decide⟩ 3
private def partial942 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 3)

private def cache943 : Cache :=
  step cache942 ⟨18, by decide⟩ 0
private def partial943 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 0)

private def cache944 : Cache :=
  step cache943 ⟨19, by decide⟩ 0
private def partial944 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 0)

private def cache945 : Cache :=
  step cache943 ⟨19, by decide⟩ 1
private def partial945 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 1)

private def cache946 : Cache :=
  step cache943 ⟨19, by decide⟩ 2
private def partial946 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 2)

private def cache947 : Cache :=
  step cache943 ⟨19, by decide⟩ 3
private def partial947 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 3)

private def cache948 : Cache :=
  step cache942 ⟨18, by decide⟩ 1
private def partial948 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 1)

private def cache949 : Cache :=
  step cache948 ⟨19, by decide⟩ 0
private def partial949 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 0)

private def cache950 : Cache :=
  step cache948 ⟨19, by decide⟩ 1
private def partial950 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 1)

private def cache951 : Cache :=
  step cache948 ⟨19, by decide⟩ 2
private def partial951 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 2)

private def cache952 : Cache :=
  step cache948 ⟨19, by decide⟩ 3
private def partial952 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 3)

private def cache953 : Cache :=
  step cache942 ⟨18, by decide⟩ 2
private def partial953 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 2)

private def cache954 : Cache :=
  step cache942 ⟨18, by decide⟩ 3
private def partial954 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 3)

private theorem receipt954 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨954, by decide⟩ cache954 partial954 = true := by
  decide +kernel

private theorem receipt953 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨953, by decide⟩ cache953 partial953 = true := by
  decide +kernel

private theorem receipt952 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨952, by decide⟩ cache952 partial952 = true := by
  decide +kernel

private theorem receipt951 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨951, by decide⟩ cache951 partial951 = true := by
  decide +kernel

private theorem receipt950 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨950, by decide⟩ cache950 partial950 = true := by
  decide +kernel

private theorem receipt949 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨949, by decide⟩ cache949 partial949 = true := by
  decide +kernel

private theorem receipt948 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨948, by decide⟩ cache948 partial948 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![949,950,951,952])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2093980828071603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt949
  · exact receipt950
  · exact receipt951
  · exact receipt952

private theorem receipt947 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨947, by decide⟩ cache947 partial947 = true := by
  decide +kernel

private theorem receipt946 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨946, by decide⟩ cache946 partial946 = true := by
  decide +kernel

private theorem receipt945 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨945, by decide⟩ cache945 partial945 = true := by
  decide +kernel

private theorem receipt944 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨944, by decide⟩ cache944 partial944 = true := by
  decide +kernel

private theorem receipt943 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨943, by decide⟩ cache943 partial943 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![944,945,946,947])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2082983026783763 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt944
  · exact receipt945
  · exact receipt946
  · exact receipt947

private theorem receipt942 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨942, by decide⟩ cache942 partial942 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![943,948,953,954])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2098379948062194 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt943
  · exact receipt948
  · exact receipt953
  · exact receipt954

private theorem receipt941 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨941, by decide⟩ cache941 partial941 = true := by
  decide +kernel

private theorem receipt940 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨940, by decide⟩ cache940 partial940 = true := by
  decide +kernel

private theorem receipt939 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨939, by decide⟩ cache939 partial939 = true := by
  decide +kernel

private theorem receipt938 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨938, by decide⟩ cache938 partial938 = true := by
  decide +kernel

private theorem receipt937 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨937, by decide⟩ cache937 partial937 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![938,939,940,941])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2069785665238355 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt938
  · exact receipt939
  · exact receipt940
  · exact receipt941

private theorem receipt936 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨936, by decide⟩ cache936 partial936 = true := by
  decide +kernel

private theorem receipt935 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨935, by decide⟩ cache935 partial935 = true := by
  decide +kernel

private theorem receipt934 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨934, by decide⟩ cache934 partial934 = true := by
  decide +kernel

private theorem receipt933 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨933, by decide⟩ cache933 partial933 = true := by
  decide +kernel

private theorem receipt932 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨932, by decide⟩ cache932 partial932 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![933,934,935,936])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2058787863950515 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt933
  · exact receipt934
  · exact receipt935
  · exact receipt936

private theorem receipt931 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨931, by decide⟩ cache931 partial931 = true := by
  decide +kernel

private theorem receipt930 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨930, by decide⟩ cache930 partial930 = true := by
  decide +kernel

private theorem receipt929 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨929, by decide⟩ cache929 partial929 = true := by
  decide +kernel

private theorem receipt928 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨928, by decide⟩ cache928 partial928 = true := by
  decide +kernel

private theorem receipt927 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨927, by decide⟩ cache927 partial927 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![928,929,930,931])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2047790062662675 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt928
  · exact receipt929
  · exact receipt930
  · exact receipt931

private theorem receipt926 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨926, by decide⟩ cache926 partial926 = true := by
  decide +kernel

private theorem receipt925 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨925, by decide⟩ cache925 partial925 = true := by
  decide +kernel

private theorem receipt924 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨924, by decide⟩ cache924 partial924 = true := by
  decide +kernel

private theorem receipt923 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨923, by decide⟩ cache923 partial923 = true := by
  decide +kernel

private theorem receipt922 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨922, by decide⟩ cache922 partial922 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![923,924,925,926])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2036792261374835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt923
  · exact receipt924
  · exact receipt925
  · exact receipt926

private theorem receipt921 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨921, by decide⟩ cache921 partial921 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![922,927,932,937])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2060985275675474 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt922
  · exact receipt927
  · exact receipt932
  · exact receipt937

private theorem receipt920 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨920, by decide⟩ cache920 partial920 = true := by
  decide +kernel

private theorem receipt919 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨919, by decide⟩ cache919 partial919 = true := by
  decide +kernel

private theorem receipt918 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨918, by decide⟩ cache918 partial918 = true := by
  decide +kernel

private theorem receipt917 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨917, by decide⟩ cache917 partial917 = true := by
  decide +kernel

private theorem receipt916 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨916, by decide⟩ cache916 partial916 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![917,918,919,920])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2023594899829427 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt917
  · exact receipt918
  · exact receipt919
  · exact receipt920

private theorem receipt915 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨915, by decide⟩ cache915 partial915 = true := by
  decide +kernel

private theorem receipt914 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨914, by decide⟩ cache914 partial914 = true := by
  decide +kernel

private theorem receipt913 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨913, by decide⟩ cache913 partial913 = true := by
  decide +kernel

private theorem receipt912 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨912, by decide⟩ cache912 partial912 = true := by
  decide +kernel

private theorem receipt911 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨911, by decide⟩ cache911 partial911 = true := by
  decide +kernel

private theorem receipt910 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨910, by decide⟩ cache910 partial910 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![911,912,913,914])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2010397538284019 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt911
  · exact receipt912
  · exact receipt913
  · exact receipt914

private theorem receipt909 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨909, by decide⟩ cache909 partial909 = true := by
  decide +kernel

private theorem receipt908 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨908, by decide⟩ cache908 partial908 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![909,910,915,916])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2014796658274738 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt909
  · exact receipt910
  · exact receipt915
  · exact receipt916

private theorem receipt907 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨907, by decide⟩ cache907 partial907 = true := by
  decide +kernel

theorem receipt906 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨906, by decide⟩ cache906 partial906 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![907,908,921,942])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2071974483882353 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt907
  · exact receipt908
  · exact receipt921
  · exact receipt942

private theorem receipt905 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨905, by decide⟩ cache905 partial905 = true := by
  decide +kernel

private theorem receipt904 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨904, by decide⟩ cache904 partial904 = true := by
  decide +kernel

private theorem receipt903 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨903, by decide⟩ cache903 partial903 = true := by
  decide +kernel

private theorem receipt902 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨902, by decide⟩ cache902 partial902 = true := by
  decide +kernel

private theorem receipt901 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨901, by decide⟩ cache901 partial901 = true := by
  decide +kernel

private theorem receipt900 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨900, by decide⟩ cache900 partial900 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![901,902,903,904])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1988401935708339 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt901
  · exact receipt902
  · exact receipt903
  · exact receipt904

private theorem receipt899 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨899, by decide⟩ cache899 partial899 = true := by
  decide +kernel

private theorem receipt898 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨898, by decide⟩ cache898 partial898 = true := by
  decide +kernel

private theorem receipt897 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨897, by decide⟩ cache897 partial897 = true := by
  decide +kernel

private theorem receipt896 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨896, by decide⟩ cache896 partial896 = true := by
  decide +kernel

private theorem receipt895 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨895, by decide⟩ cache895 partial895 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![896,897,898,899])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1977404134420499 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt896
  · exact receipt897
  · exact receipt898
  · exact receipt899

private theorem receipt894 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨894, by decide⟩ cache894 partial894 = true := by
  decide +kernel

private theorem receipt893 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨893, by decide⟩ cache893 partial893 = true := by
  decide +kernel

private theorem receipt892 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨892, by decide⟩ cache892 partial892 = true := by
  decide +kernel

private theorem receipt891 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨891, by decide⟩ cache891 partial891 = true := by
  decide +kernel

private theorem receipt890 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨890, by decide⟩ cache890 partial890 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![891,892,893,894])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1966406333132659 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt891
  · exact receipt892
  · exact receipt893
  · exact receipt894

private theorem receipt889 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨889, by decide⟩ cache889 partial889 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![890,895,900,905])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1990599347433298 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt890
  · exact receipt895
  · exact receipt900
  · exact receipt905

private theorem receipt888 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨888, by decide⟩ cache888 partial888 = true := by
  decide +kernel

private theorem receipt887 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨887, by decide⟩ cache887 partial887 = true := by
  decide +kernel

private theorem receipt886 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨886, by decide⟩ cache886 partial886 = true := by
  decide +kernel

private theorem receipt885 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨885, by decide⟩ cache885 partial885 = true := by
  decide +kernel

private theorem receipt884 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨884, by decide⟩ cache884 partial884 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![885,886,887,888])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1953208971587251 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt885
  · exact receipt886
  · exact receipt887
  · exact receipt888

private theorem receipt883 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨883, by decide⟩ cache883 partial883 = true := by
  decide +kernel

private theorem receipt882 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨882, by decide⟩ cache882 partial882 = true := by
  decide +kernel

private theorem receipt881 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨881, by decide⟩ cache881 partial881 = true := by
  decide +kernel

private theorem receipt880 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨880, by decide⟩ cache880 partial880 = true := by
  decide +kernel

private theorem receipt879 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨879, by decide⟩ cache879 partial879 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![880,881,882,883])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1942211170299411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt880
  · exact receipt881
  · exact receipt882
  · exact receipt883

private theorem receipt878 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨878, by decide⟩ cache878 partial878 = true := by
  decide +kernel

private theorem receipt877 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨877, by decide⟩ cache877 partial877 = true := by
  decide +kernel

private theorem receipt876 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨876, by decide⟩ cache876 partial876 = true := by
  decide +kernel

private theorem receipt875 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨875, by decide⟩ cache875 partial875 = true := by
  decide +kernel

private theorem receipt874 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨874, by decide⟩ cache874 partial874 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![875,876,877,878])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1931213369011571 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt875
  · exact receipt876
  · exact receipt877
  · exact receipt878

private theorem receipt873 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨873, by decide⟩ cache873 partial873 = true := by
  decide +kernel

private theorem receipt872 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨872, by decide⟩ cache872 partial872 = true := by
  decide +kernel

private theorem receipt871 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨871, by decide⟩ cache871 partial871 = true := by
  decide +kernel

private theorem receipt870 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨870, by decide⟩ cache870 partial870 = true := by
  decide +kernel

private theorem receipt869 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨869, by decide⟩ cache869 partial869 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![870,871,872,873])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1920215567723731 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt870
  · exact receipt871
  · exact receipt872
  · exact receipt873

private theorem receipt868 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨868, by decide⟩ cache868 partial868 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![869,874,879,884])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1944408582024370 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt869
  · exact receipt874
  · exact receipt879
  · exact receipt884

private theorem receipt867 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨867, by decide⟩ cache867 partial867 = true := by
  decide +kernel

private theorem receipt866 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨866, by decide⟩ cache866 partial866 = true := by
  decide +kernel

theorem receipt865 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨865, by decide⟩ cache865 partial865 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![866,867,868,889])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1955397791804497 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt866
  · exact receipt867
  · exact receipt868
  · exact receipt889

theorem receipt864 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨864, by decide⟩ cache864 partial864 = true := by
  decide +kernel

theorem receipt863 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨863, by decide⟩ cache863 partial863 = true := by
  decide +kernel

theorem receipt861 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨861, by decide⟩ cache861 partial861 = true := by
  decide +kernel

theorem receipt860 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨860, by decide⟩ cache860 partial860 = true := by
  decide +kernel

private theorem receipt857 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨857, by decide⟩ cache857 partial857 = true := by
  decide +kernel

private theorem receipt856 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨856, by decide⟩ cache856 partial856 = true := by
  decide +kernel

private theorem receipt855 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨855, by decide⟩ cache855 partial855 = true := by
  decide +kernel

private theorem receipt854 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨854, by decide⟩ cache854 partial854 = true := by
  decide +kernel

private theorem receipt853 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨853, by decide⟩ cache853 partial853 = true := by
  decide +kernel

private theorem receipt852 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨852, by decide⟩ cache852 partial852 = true := by
  decide +kernel

private theorem receipt851 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨851, by decide⟩ cache851 partial851 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![852,853,854,855])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1880623483087507 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt852
  · exact receipt853
  · exact receipt854
  · exact receipt855

private theorem receipt850 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨850, by decide⟩ cache850 partial850 = true := by
  decide +kernel

private theorem receipt849 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨849, by decide⟩ cache849 partial849 = true := by
  decide +kernel

private theorem receipt848 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨848, by decide⟩ cache848 partial848 = true := by
  decide +kernel

private theorem receipt847 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨847, by decide⟩ cache847 partial847 = true := by
  decide +kernel

private theorem receipt846 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨846, by decide⟩ cache846 partial846 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![847,848,849,850])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1869625681799667 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt847
  · exact receipt848
  · exact receipt849
  · exact receipt850

private theorem receipt845 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨845, by decide⟩ cache845 partial845 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![846,851,856,857])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1885022603078098 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt846
  · exact receipt851
  · exact receipt856
  · exact receipt857

private theorem receipt844 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨844, by decide⟩ cache844 partial844 = true := by
  decide +kernel

private theorem receipt843 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨843, by decide⟩ cache843 partial843 = true := by
  decide +kernel

private theorem receipt842 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨842, by decide⟩ cache842 partial842 = true := by
  decide +kernel

private theorem receipt841 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨841, by decide⟩ cache841 partial841 = true := by
  decide +kernel

private theorem receipt840 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨840, by decide⟩ cache840 partial840 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![841,842,843,844])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1856428320254258 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt841
  · exact receipt842
  · exact receipt843
  · exact receipt844

private theorem receipt839 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨839, by decide⟩ cache839 partial839 = true := by
  decide +kernel

private theorem receipt838 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨838, by decide⟩ cache838 partial838 = true := by
  decide +kernel

private theorem receipt837 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨837, by decide⟩ cache837 partial837 = true := by
  decide +kernel

private theorem receipt836 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨836, by decide⟩ cache836 partial836 = true := by
  decide +kernel

private theorem receipt835 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨835, by decide⟩ cache835 partial835 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![836,837,838,839])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1845430518966419 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt836
  · exact receipt837
  · exact receipt838
  · exact receipt839

private theorem receipt834 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨834, by decide⟩ cache834 partial834 = true := by
  decide +kernel

private theorem receipt833 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨833, by decide⟩ cache833 partial833 = true := by
  decide +kernel

private theorem receipt832 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨832, by decide⟩ cache832 partial832 = true := by
  decide +kernel

private theorem receipt831 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨831, by decide⟩ cache831 partial831 = true := by
  decide +kernel

private theorem receipt830 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨830, by decide⟩ cache830 partial830 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![831,832,833,834])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1834432717678579 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt831
  · exact receipt832
  · exact receipt833
  · exact receipt834

private theorem receipt829 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨829, by decide⟩ cache829 partial829 = true := by
  decide +kernel

private theorem receipt828 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨828, by decide⟩ cache828 partial828 = true := by
  decide +kernel

private theorem receipt827 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨827, by decide⟩ cache827 partial827 = true := by
  decide +kernel

private theorem receipt826 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨826, by decide⟩ cache826 partial826 = true := by
  decide +kernel

private theorem receipt825 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨825, by decide⟩ cache825 partial825 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![826,827,828,829])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1823434916390739 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt826
  · exact receipt827
  · exact receipt828
  · exact receipt829

private theorem receipt824 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨824, by decide⟩ cache824 partial824 = true := by
  decide +kernel

private theorem receipt823 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨823, by decide⟩ cache823 partial823 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![824,825,830,835])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1836630129403666 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt824
  · exact receipt825
  · exact receipt830
  · exact receipt835

private theorem receipt822 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨822, by decide⟩ cache822 partial822 = true := by
  decide +kernel

theorem receipt821 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨821, by decide⟩ cache821 partial821 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![822,823,840,845])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1858625730406097 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt822
  · exact receipt823
  · exact receipt840
  · exact receipt845

private theorem receipt820 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨820, by decide⟩ cache820 partial820 = true := by
  decide +kernel

private theorem receipt819 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨819, by decide⟩ cache819 partial819 = true := by
  decide +kernel

private theorem receipt818 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨818, by decide⟩ cache818 partial818 = true := by
  decide +kernel

private theorem receipt817 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨817, by decide⟩ cache817 partial817 = true := by
  decide +kernel

private theorem receipt816 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨816, by decide⟩ cache816 partial816 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![817,818,819,820])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1803638874072627 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt817
  · exact receipt818
  · exact receipt819
  · exact receipt820

private theorem receipt815 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨815, by decide⟩ cache815 partial815 = true := by
  decide +kernel

private theorem receipt814 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨814, by decide⟩ cache814 partial814 = true := by
  decide +kernel

private theorem receipt813 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨813, by decide⟩ cache813 partial813 = true := by
  decide +kernel

private theorem receipt812 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨812, by decide⟩ cache812 partial812 = true := by
  decide +kernel

private theorem receipt811 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨811, by decide⟩ cache811 partial811 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![812,813,814,815])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1792641072784787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt812
  · exact receipt813
  · exact receipt814
  · exact receipt815

private theorem receipt810 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨810, by decide⟩ cache810 partial810 = true := by
  decide +kernel

private theorem receipt809 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨809, by decide⟩ cache809 partial809 = true := by
  decide +kernel

private theorem receipt808 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨808, by decide⟩ cache808 partial808 = true := by
  decide +kernel

private theorem receipt807 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨807, by decide⟩ cache807 partial807 = true := by
  decide +kernel

private theorem receipt806 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨806, by decide⟩ cache806 partial806 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![807,808,809,810])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1781643271496947 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt807
  · exact receipt808
  · exact receipt809
  · exact receipt810

private theorem receipt805 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨805, by decide⟩ cache805 partial805 = true := by
  decide +kernel

private theorem receipt804 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨804, by decide⟩ cache804 partial804 = true := by
  decide +kernel

private theorem receipt803 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨803, by decide⟩ cache803 partial803 = true := by
  decide +kernel

private theorem receipt802 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨802, by decide⟩ cache802 partial802 = true := by
  decide +kernel

private theorem receipt801 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨801, by decide⟩ cache801 partial801 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![802,803,804,805])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1770645470209107 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt802
  · exact receipt803
  · exact receipt804
  · exact receipt805

private theorem receipt800 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨800, by decide⟩ cache800 partial800 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![801,806,811,816])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1794838484509746 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt801
  · exact receipt806
  · exact receipt811
  · exact receipt816

private theorem receipt799 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨799, by decide⟩ cache799 partial799 = true := by
  decide +kernel

private theorem receipt798 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨798, by decide⟩ cache798 partial798 = true := by
  decide +kernel

private theorem receipt797 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨797, by decide⟩ cache797 partial797 = true := by
  decide +kernel

private theorem receipt796 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨796, by decide⟩ cache796 partial796 = true := by
  decide +kernel

private theorem receipt795 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨795, by decide⟩ cache795 partial795 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![796,797,798,799])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1757448108663698 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt796
  · exact receipt797
  · exact receipt798
  · exact receipt799

private theorem receipt794 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨794, by decide⟩ cache794 partial794 = true := by
  decide +kernel

private theorem receipt793 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨793, by decide⟩ cache793 partial793 = true := by
  decide +kernel

private theorem receipt792 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨792, by decide⟩ cache792 partial792 = true := by
  decide +kernel

private theorem receipt791 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨791, by decide⟩ cache791 partial791 = true := by
  decide +kernel

private theorem receipt790 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨790, by decide⟩ cache790 partial790 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![791,792,793,794])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1746450307375859 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt791
  · exact receipt792
  · exact receipt793
  · exact receipt794

private theorem receipt789 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨789, by decide⟩ cache789 partial789 = true := by
  decide +kernel

private theorem receipt788 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨788, by decide⟩ cache788 partial788 = true := by
  decide +kernel

private theorem receipt787 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨787, by decide⟩ cache787 partial787 = true := by
  decide +kernel

private theorem receipt786 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨786, by decide⟩ cache786 partial786 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![787,788,789,790])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1737652066345586 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt787
  · exact receipt788
  · exact receipt789
  · exact receipt790

private theorem receipt785 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨785, by decide⟩ cache785 partial785 = true := by
  decide +kernel

theorem receipt784 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨784, by decide⟩ cache784 partial784 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![785,786,795,800])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1759645519864369 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt785
  · exact receipt786
  · exact receipt795
  · exact receipt800

theorem receipt783 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨783, by decide⟩ cache783 partial783 = true := by
  decide +kernel

theorem receipt782 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨782, by decide⟩ cache782 partial782 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock9
