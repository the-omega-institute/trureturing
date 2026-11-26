/- GID: D5/S3/Combinatorics/Golomb/NotikSubtrees10B
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikCheck10.archivedCertificate10; instance=D5/S3/Combinatorics/Golomb/NotikCheck10.archivedCertificate10
   digest: Exact lower-bound and equality checks for 10 marks, group B. -/

import D5.S3.Combinatorics.Golomb.NotikData10
import D5.S3.Combinatorics.Golomb.NotikLeaves10B
import D5.S3.Combinatorics.Golomb.NotikSubtreeReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group10

theorem certificate6601 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path6601 Archive10.subtree6601 leaves6601 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate6602 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path6602 Archive10.subtree6602 leaves6602 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate399 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path399 Archive10.subtree399 leaves399 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate401 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path401 Archive10.subtree401 leaves401 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate403 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path403 Archive10.subtree403 leaves403 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate405 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path405 Archive10.subtree405 leaves405 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate406 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path406 Archive10.subtree406 leaves406 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

theorem certificate4 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path4 Archive10.subtree4 leaves4 :=
  ⟨by decide +kernel, finishedCover_sound (by decide +kernel)⟩

end Group10

end D5.S3.Combinatorics.Golomb.NotikMinimizers
