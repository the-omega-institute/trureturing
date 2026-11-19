/- GID: D5/S3/Combinatorics/Golomb/NotikCheck9
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikMinimizers.result; instance=D5/S3/Combinatorics/Golomb/NotikCheck9.archivedCertificate9
   digest: The complete archived lower-bound and equality checks hold for 9 marks. -/

import D5.S3.Combinatorics.Golomb.NotikSubtrees9A
import D5.S3.Combinatorics.Golomb.NotikSubtrees9B

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group9

private theorem certificate9895 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9895 Archive9.subtree9895 leaves9895 :=
  SubtreeCertificate.branch witnessIndex9895 certificate13493 certificate13494

private theorem certificate9902 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9902 Archive9.subtree9902 leaves9902 :=
  SubtreeCertificate.branch witnessIndex9902 certificate9903 certificate9904

private theorem certificate9900 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9900 Archive9.subtree9900 leaves9900 :=
  SubtreeCertificate.branch witnessIndex9900 certificate9901 certificate9902

private theorem certificate9898 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9898 Archive9.subtree9898 leaves9898 :=
  SubtreeCertificate.branch witnessIndex9898 certificate9899 certificate9900

private theorem certificate9896 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9896 Archive9.subtree9896 leaves9896 :=
  SubtreeCertificate.branch witnessIndex9896 certificate9897 certificate9898

private theorem certificate1633 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1633 Archive9.subtree1633 leaves1633 :=
  SubtreeCertificate.branch witnessIndex1633 certificate9895 certificate9896

private theorem certificate5204 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path5204 Archive9.subtree5204 leaves5204 :=
  SubtreeCertificate.branch witnessIndex5204 certificate5205 certificate5206

private theorem certificate5202 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path5202 Archive9.subtree5202 leaves5202 :=
  SubtreeCertificate.branch witnessIndex5202 certificate5203 certificate5204

private theorem certificate4473 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path4473 Archive9.subtree4473 leaves4473 :=
  SubtreeCertificate.branch witnessIndex4473 certificate5201 certificate5202

private theorem certificate1635 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1635 Archive9.subtree1635 leaves1635 :=
  SubtreeCertificate.branch witnessIndex1635 certificate4473 certificate4474

private theorem certificate1636 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1636 Archive9.subtree1636 leaves1636 :=
  SubtreeCertificate.branch witnessIndex1636 certificate1637 certificate1638

private theorem certificate1634 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1634 Archive9.subtree1634 leaves1634 :=
  SubtreeCertificate.branch witnessIndex1634 certificate1635 certificate1636

private theorem certificate1 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1 Archive9.subtree1 leaves1 :=
  SubtreeCertificate.branch witnessIndex1 certificate1633 certificate1634

private theorem certificate0 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses [] Archive9.tree leafTable9 :=
  SubtreeCertificate.branch witnessIndex0 certificate1 certificate2

end Group9

theorem archivedCertificate9 :
    checkStatic Archive9.data archiveBounds = true ∧
    Archive9.tree.check Archive9.target (staticRows Archive9.data) (relationRows Archive9.witnesses) [] = true ∧
    Archive9.tree.cover Archive9.target Archive9.data Archive9.witnesses [] Group9.leafTable9 = some [] :=
  ⟨by decide +kernel, Group9.certificate0.checked, Group9.certificate0.covered⟩

end D5.S3.Combinatorics.Golomb.NotikMinimizers
