/- GID: D5/S3/Combinatorics/Golomb/NotikSubtrees8A
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: Exact lower-bound and equality checks for 8 marks, group A. -/

import D5.S3.Combinatorics.Golomb.NotikData8
import D5.S3.Combinatorics.Golomb.NotikSubtreeReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group8

theorem certificate1 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses path1 Archive8.subtree1 leaves1 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate465 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses path465 Archive8.subtree465 leaves465 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

end Group8

end D5.S3.Combinatorics.Golomb.NotikMinimizers
