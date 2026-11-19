/- GID: D5/S3/Combinatorics/Golomb/NotikSubtrees9B
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck9.archivedCertificate9; instance=D5/S3/Combinatorics/Golomb/NotikCheck9.archivedCertificate9
   digest: Exact lower-bound and equality checks for 9 marks, group B. -/

import D5.S3.Combinatorics.Golomb.NotikData9
import D5.S3.Combinatorics.Golomb.NotikLeaves9B
import D5.S3.Combinatorics.Golomb.NotikSubtreeReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group9

theorem certificate5201 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path5201 Archive9.subtree5201 leaves5201 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate5203 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path5203 Archive9.subtree5203 leaves5203 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate5205 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path5205 Archive9.subtree5205 leaves5205 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate5206 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path5206 Archive9.subtree5206 leaves5206 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate4474 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path4474 Archive9.subtree4474 leaves4474 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate1637 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1637 Archive9.subtree1637 leaves1637 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate1638 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path1638 Archive9.subtree1638 leaves1638 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate2 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path2 Archive9.subtree2 leaves2 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

end Group9

end D5.S3.Combinatorics.Golomb.NotikMinimizers
