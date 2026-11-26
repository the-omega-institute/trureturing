/- GID: D5/S3/Combinatorics/Golomb/NotikSubtrees9A
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck9.archivedCertificate9; instance=D5/S3/Combinatorics/Golomb/NotikCheck9.archivedCertificate9
   digest: Exact lower-bound and equality checks for 9 marks, group A. -/

import D5.S3.Combinatorics.Golomb.NotikData9
import D5.S3.Combinatorics.Golomb.NotikLeaves9A
import D5.S3.Combinatorics.Golomb.NotikSubtreeReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group9

theorem certificate13493 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path13493 Archive9.subtree13493 leaves13493 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate13494 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path13494 Archive9.subtree13494 leaves13494 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate9897 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9897 Archive9.subtree9897 leaves9897 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate9899 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9899 Archive9.subtree9899 leaves9899 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate9901 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9901 Archive9.subtree9901 leaves9901 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate9903 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9903 Archive9.subtree9903 leaves9903 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate9904 :
    SubtreeCertificate Archive9.target Archive9.data Archive9.witnesses path9904 Archive9.subtree9904 leaves9904 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

end Group9

end D5.S3.Combinatorics.Golomb.NotikMinimizers
