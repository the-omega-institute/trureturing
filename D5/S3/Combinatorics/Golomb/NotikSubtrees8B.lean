/- GID: D5/S3/Combinatorics/Golomb/NotikSubtrees8B
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: Exact lower-bound and equality checks for 8 marks, group B. -/

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

theorem certificate466 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses path466 Archive8.subtree466 leaves466 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate4 :
    SubtreeCertificate Archive8.target Archive8.data Archive8.witnesses path4 Archive8.subtree4 leaves4 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

end Group8

end D5.S3.Combinatorics.Golomb.NotikMinimizers
