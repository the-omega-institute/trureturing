/- GID: D5/S3/Combinatorics/Golomb/NotikCheck10
   generality: I
   mirror-B: none(waiver:covered-by-notik-minimizers-blueprint)
   mirror-E: none(waiver:kernel-replayed-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Golomb/NotikMinimizers.result; instance=D5/S3/Combinatorics/Golomb/NotikCheck10.archivedCertificate10
   digest: The complete archived lower-bound and equality checks hold for 10 marks. -/

import D5.S3.Combinatorics.Golomb.NotikSubtrees10A
import D5.S3.Combinatorics.Golomb.NotikSubtrees10B

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay

namespace Group10

private theorem certificate14327 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path14327 Archive10.subtree14327 leaves14327 :=
  SubtreeCertificate.branch witnessIndex14327 certificate15841 certificate15842

private theorem certificate11675 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path11675 Archive10.subtree11675 leaves11675 :=
  SubtreeCertificate.branch witnessIndex11675 certificate14327 certificate14328

private theorem certificate11676 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path11676 Archive10.subtree11676 leaves11676 :=
  SubtreeCertificate.branch witnessIndex11676 certificate11677 certificate11678

private theorem certificate10323 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path10323 Archive10.subtree10323 leaves10323 :=
  SubtreeCertificate.branch witnessIndex10323 certificate11675 certificate11676

private theorem certificate6597 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path6597 Archive10.subtree6597 leaves6597 :=
  SubtreeCertificate.branch witnessIndex6597 certificate10323 certificate10324

private theorem certificate6600 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path6600 Archive10.subtree6600 leaves6600 :=
  SubtreeCertificate.branch witnessIndex6600 certificate6601 certificate6602

private theorem certificate6598 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path6598 Archive10.subtree6598 leaves6598 :=
  SubtreeCertificate.branch witnessIndex6598 certificate6599 certificate6600

private theorem certificate1 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path1 Archive10.subtree1 leaves1 :=
  SubtreeCertificate.branch witnessIndex1 certificate6597 certificate6598

private theorem certificate404 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path404 Archive10.subtree404 leaves404 :=
  SubtreeCertificate.branch witnessIndex404 certificate405 certificate406

private theorem certificate402 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path402 Archive10.subtree402 leaves402 :=
  SubtreeCertificate.branch witnessIndex402 certificate403 certificate404

private theorem certificate400 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path400 Archive10.subtree400 leaves400 :=
  SubtreeCertificate.branch witnessIndex400 certificate401 certificate402

private theorem certificate3 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path3 Archive10.subtree3 leaves3 :=
  SubtreeCertificate.branch witnessIndex3 certificate399 certificate400

private theorem certificate2 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses path2 Archive10.subtree2 leaves2 :=
  SubtreeCertificate.branch witnessIndex2 certificate3 certificate4

private theorem certificate0 :
    SubtreeCertificate Archive10.target Archive10.data Archive10.witnesses [] Archive10.tree leafTable10 :=
  SubtreeCertificate.branch witnessIndex0 certificate1 certificate2

end Group10

theorem archivedCertificate10 :
    checkStatic Archive10.data archiveBounds = true ∧
    Archive10.tree.check Archive10.target (staticRows Archive10.data) (relationRows Archive10.witnesses) [] = true ∧
    Archive10.tree.cover Archive10.target Archive10.data Archive10.witnesses [] Group10.leafTable10 = some [] :=
  ⟨by decide +kernel, Group10.certificate0.checked, Group10.certificate0.covered⟩

end D5.S3.Combinatorics.Golomb.NotikMinimizers
