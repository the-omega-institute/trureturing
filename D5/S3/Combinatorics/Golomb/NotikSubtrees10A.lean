/- GID: D5/S3/Combinatorics/Golomb/NotikSubtrees10A
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck10.archivedCertificate10; instance=D5/S3/Combinatorics/Golomb/NotikCheck10.archivedCertificate10
   digest: Exact lower-bound and equality checks for 10 marks, group A. -/

import D5.S3.Combinatorics.Golomb.NotikData10
import D5.S3.Combinatorics.Golomb.NotikLeaves10A
import D5.S3.Combinatorics.Golomb.NotikSubtreeReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group10

theorem certificate15841 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path15841 Archive10.subtree15841 leaves15841 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate15842 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path15842 Archive10.subtree15842 leaves15842 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate14328 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path14328 Archive10.subtree14328 leaves14328 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate11677 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path11677 Archive10.subtree11677 leaves11677 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate11678 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path11678 Archive10.subtree11678 leaves11678 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate10324 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path10324 Archive10.subtree10324 leaves10324 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate6599 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path6599 Archive10.subtree6599 leaves6599 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

end Group10

end D5.S3.Combinatorics.Golomb.NotikMinimizers
