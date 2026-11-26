/- GID: D5/S3/Combinatorics/Golomb/NotikCheck8
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikMinimizers.result; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: The complete archived lower-bound and equality checks hold for 8 marks. -/

import D5.S3.Combinatorics.Golomb.NotikSubtrees8A
import D5.S3.Combinatorics.Golomb.NotikSubtrees8B

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group8

private theorem certificate3 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses path3 Archive8.subtree3 leaves3 :=
  SubtreeCertificate.branch witnessIndex3 certificate465 certificate466

private theorem certificate2 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses path2 Archive8.subtree2 leaves2 :=
  SubtreeCertificate.branch witnessIndex2 certificate3 certificate4

private theorem certificate0 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses [] Archive8.archivedTree8 leafTable8 :=
  SubtreeCertificate.branch witnessIndex0 certificate1 certificate2

end Group8

theorem archivedCertificate8 :
    checkStatic Archive8.data archiveBounds = true ∧
    Archive8.archivedTree8.check Archive8.target (staticRows Archive8.data) (relationRows Archive8.witnesses) [] = true ∧
    Archive8.archivedTree8.cover Archive8.target Archive8.data Archive8.witnesses [] Group8.leafTable8 = some [] :=
  ⟨by decide +kernel, Group8.certificate0.checked, Group8.certificate0.covered⟩

end D5.S3.Combinatorics.Golomb.NotikMinimizers
