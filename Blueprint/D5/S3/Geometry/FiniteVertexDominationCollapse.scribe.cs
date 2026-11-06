using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

// UNCOMPILED Scribe source attempt. No C# / Scribe / Lean native checks ran.
internal sealed class FiniteVertexDominationCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteVertexDominationCollapse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-label dominated-vertex elementary collapse certificates.",
        H("Finite dominated-vertex free-face deletion"),
        Blocks(
            Paragraph(Text("SOURCE ATTEMPT: all listed Lean declarations are UNCOMPILED. "
                + "The raw headers below are written in the section V : Type*, Fintype V, DecidableEq V. "
                + "Unused section instances may not be captured; native binder closures are unobserved. "
                + "K is a native PreAbstractSimplicialComplex, with nonempty faces only. "
                + "No carrier, purity, connectedness, or realization-nonempty hypothesis is hidden. "
                + "Canonical finite relative and elementary owners supply the native Sequence and SDR. "
                + "This is the classical decreasing-face pairing proof, credited to the released "
                + "CLI79532 ordinary verification, constructive_restricted_result.K_elementary_fold "
                + "and actual_Ind_F_certificate.graph_fold; no novelty is claimed.")),
            Node("extends", "Extends", "Extends",
                "For every face s of K containing v, insert u s is again a face. This is the sole combinatorial extension hypothesis and contains no collapse or geometric endpoint.",
                "def Extends (K : PreAbstractSimplicialComplex V) (u v : V) : Prop", DescribeRole.Definition),
            Node("badfaces", "badFaces", "badFaces",
                "The finite family consists exactly of original faces containing v and omitting u; the empty face is absent.",
                "def badFaces (K : PreAbstractSimplicialComplex V) (u v : V) : Finset (Finset V)", DescribeRole.Definition),
            Node("mem-badfaces", "mem_badFaces", "mem_badFaces",
                "Membership is exactly the three stated original-face conditions.",
                "@[simp] theorem mem_badFaces (K : PreAbstractSimplicialComplex V) (u v : V)\n    (s : Finset V) : s ∈ badFaces K u v ↔ s ∈ K ∧ v ∈ s ∧ u ∉ s", DescribeRole.Theorem),
            Node("faceset", "faceSet", "faceSet",
                "All actual nonempty faces of K on V, collected as a finite set.",
                "def faceSet (K : PreAbstractSimplicialComplex V) : Finset (Finset V)", DescribeRole.Definition),
            Node("mem-faceset", "mem_faceSet", "mem_faceSet",
                "The finite face family has exactly the original complex membership.",
                "@[simp] theorem mem_faceSet (K : PreAbstractSimplicialComplex V) (s : Finset V) :\n    s ∈ faceSet K ↔ s ∈ K", DescribeRole.Theorem),
            Node("badfaces-empty-iff", "badFaces_empty_iff", "badFaces_empty_iff",
                "For distinct u and v, the lower-face family is empty exactly when v is a ghost of K. A singleton v witnesses the converse direction whenever v occurs in any face.",
                "theorem badFaces_empty_iff (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) : badFaces K u v = ∅ ↔ Fresh v K", DescribeRole.Theorem),
            Node("sequence", "sequence", "sequence",
                "For distinct u and v under Extends, construct a genuine native Sequence from K to its literal deletion of v. Strong induction on the current lower-face count selects a maximum-cardinality lower face. The proof checks its sole strict coface, retained extension invariant, and exact decrement before recursing.",
                "def sequence (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) : Sequence K (deletion K v)", DescribeRole.Definition),
            Node("orderedlowers", "orderedLowers", "orderedLowers",
                "The native sequence lower faces, in their actual removal order.",
                "def orderedLowers (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) : List (Finset V)", DescribeRole.Definition),
            Node("orderedpairs", "orderedPairs", "orderedPairs",
                "The complete native sequence list of literal lower and upper faces, in removal order.",
                "def orderedPairs (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) : List (Finset V × Finset V)", DescribeRole.Definition),
            Node("sequence-pair-spec", "sequence_pair_spec", "sequence_pair_spec",
                "Every pair has a nonempty lower containing v, omitting u, and apex exactly u, so its upper is insert u lower. Labels are never replaced by a subtype.",
                "theorem sequence_pair_spec (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (P : CollapsePair V)\n    (hP : P ∈ (sequence K u v huv hExt).pairs) :\n    P.lower.Nonempty ∧ v ∈ P.lower ∧ u ∉ P.lower ∧\n      P.apex = u ∧ P.upper = insert u P.lower", DescribeRole.Theorem),
            Node("orderedlowers-nodup", "orderedLowers_nodup", "orderedLowers_nodup",
                "No original lower face occurs twice.",
                "theorem orderedLowers_nodup (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (orderedLowers K u v huv hExt).Nodup", DescribeRole.Theorem),
            Node("orderedlowers-mem", "orderedLowers_mem", "orderedLowers_mem",
                "Every original face of K containing v and omitting u occurs, and only such faces occur. The conditions refer to the ORIGINAL K, not to an assumed current matching.",
                "theorem orderedLowers_mem (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V) :\n    s ∈ orderedLowers K u v huv hExt ↔ s ∈ K ∧ v ∈ s ∧ u ∉ s", DescribeRole.Theorem),
            Node("orderedlowers-decreasing", "orderedLowers_decreasing", "orderedLowers_decreasing",
                "For each earlier and later lower face in the list, the later cardinality is at most the earlier cardinality; ties may be resolved by classical maximum choice.",
                "theorem orderedLowers_decreasing (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (orderedLowers K u v huv hExt).Pairwise (fun s t => t.card ≤ s.card)", DescribeRole.Theorem),
            Node("orderedpairs-eq", "orderedPairs_eq", "orderedPairs_eq",
                "The complete pair list is exactly the ordered lower list mapped to (s, insert u s).",
                "theorem orderedPairs_eq (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    orderedPairs K u v huv hExt =\n      (orderedLowers K u v huv hExt).map (fun s => (s, insert u s))", DescribeRole.Theorem),
            Node("orderedpairs-nodup", "orderedPairs_nodup", "orderedPairs_nodup",
                "No ordered lower-upper pair occurs twice, since its first coordinate determines its lower face.",
                "theorem orderedPairs_nodup (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (orderedPairs K u v huv hExt).Nodup", DescribeRole.Theorem),
            Node("orderedpairs-mem", "orderedPairs_mem", "orderedPairs_mem",
                "A pair (a,b) occurs exactly when a is an original face containing v and omitting u, and b is exactly insert u a.",
                "theorem orderedPairs_mem (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (a b : Finset V) :\n    (a, b) ∈ orderedPairs K u v huv hExt ↔\n      a ∈ K ∧ v ∈ a ∧ u ∉ a ∧ b = insert u a", DescribeRole.Theorem),
            Node("sequence-length", "sequence_length", "sequence_length",
                "The number of actual native free-pair steps equals the cardinality of the complete original lower-face family.",
                "theorem sequence_length (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (sequence K u v huv hExt).pairs.length = (badFaces K u v).card", DescribeRole.Theorem),
            Node("deletion-le-each-retained", "deletion_le_each_retained", "deletion_le_each_retained",
                "Every deletion face survives every retained stage, with no connectedness or dimension restriction.",
                "theorem deletion_le_each_retained (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (P : CollapsePair V)\n    (hP : P ∈ (sequence K u v huv hExt).pairs) : deletion K v ≤ P.retained", DescribeRole.Theorem),
            Node("frames-length", "frames_length", "frames_length",
                "The frames list has n+1 entries for n original lower faces, including the final deletion frame.",
                "theorem frames_length (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (sequence K u v huv hExt).frames.length = (badFaces K u v).card + 1", DescribeRole.Theorem),
            Node("frames-initial", "frames_initial", "frames_initial",
                "The frame at index zero is literally K.",
                "theorem frames_initial (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (sequence K u v huv hExt).frames.getD 0 (deletion K v) = K", DescribeRole.Theorem),
            Node("frames-terminal", "frames_terminal", "frames_terminal",
                "The frame at index n is literally deletion K v; the getD default is also explicitly that deletion.",
                "theorem frames_terminal (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (sequence K u v huv hExt).frames.getD (badFaces K u v).card (deletion K v) =\n      deletion K v", DescribeRole.Theorem),
            Node("frame-mem-iff", "frame_mem_iff", "frame_mem_iff",
                "For every valid index i including n, membership in the actual ith complex is original K membership with precisely the lower and upper faces of the first i native pairs removed. This is a replay statement about the evolving complexes.",
                "theorem frame_mem_iff (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (i : Nat)\n    (hi : i ≤ (badFaces K u v).card) (s : Finset V) :\n    s ∈ (sequence K u v huv hExt).frames.getD i (deletion K v) ↔\n      s ∈ K ∧ ∀ P ∈ (sequence K u v huv hExt).pairs.take i,\n        s ≠ P.lower ∧ s ≠ P.upper", DescribeRole.Theorem),
            Node("face-count", "face_count", "face_count",
                "The number of original nonempty faces is the number of deletion faces plus twice the complete lower-face count. Each genuine elementary pair removes exactly two different nonempty faces.",
                "theorem face_count (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (faceSet K).card = (faceSet (deletion K v)).card + 2 * (badFaces K u v).card", DescribeRole.Theorem),
            Node("ghost-pairs", "ghost_pairs", "ghost_pairs",
                "If v is a ghost, the chosen certificate has the empty pair list. No empty-lower augmented collapse and no point in an empty realization is manufactured.",
                "theorem ghost_pairs (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (hf : Fresh v K) :\n    (sequence K u v huv hExt).pairs = []", DescribeRole.Theorem),
            Node("ghost-frames", "ghost_frames", "ghost_frames",
                "In the ghost case the complete frames list is [K], including its terminal frame. Empty complexes are allowed.",
                "theorem ghost_frames (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (hf : Fresh v K) :\n    (sequence K u v huv hExt).frames = [K]", DescribeRole.Theorem),
            Node("sdr", "sdr", "sdr",
                "Use native Sequence.realize to obtain a strong deformation retraction with the literal original-coordinate inclusion from the entire deletion. No alternative model is substituted.",
                "def sdr (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    RelativeSDR K (deletion K v) (deletion_le K v)", DescribeRole.Definition),
            Node("retraction", "retraction", "retraction",
                "The continuous retraction is the native finite composition of elementary-pair retractions.",
                "def retraction (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) : C(Space K, Space (deletion K v))", DescribeRole.Definition),
            Node("retraction-inclusion", "retraction_inclusion", "retraction_inclusion",
                "For every point of the full deletion realization, retraction after the literal realizationInclusion is exactly the point.",
                "theorem retraction_inclusion (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (y : Space (deletion K v)) :\n    retraction K u v huv hExt (realizationInclusion (deletion_le K v) y) = y", DescribeRole.Theorem),
            Node("collapsehomotopy", "collapseHomotopy", "collapseHomotopy",
                "The native relative homotopy runs from the actual identity to the literal inclusion after the sequence retraction. Its fixed set is the entire realized deletion.",
                "def collapseHomotopy (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) :\n    (ContinuousMap.id (Space K)).HomotopyRel\n      ((realizationInclusion (deletion_le K v)).comp (retraction K u v huv hExt))\n      {x | x.val ∈ realization (deletion K v)}", DescribeRole.Definition),
            Node("collapsehomotopy-fixed", "collapseHomotopy_fixed", "collapseHomotopy_fixed",
                "For every time and every ambient point whose vector lies in the deletion realization, the homotopy fixes that point, including arbitrary retained faces and components.",
                "theorem collapseHomotopy_fixed (K : PreAbstractSimplicialComplex V) (u v : V)\n    (huv : u ≠ v) (hExt : Extends K u v) (t : I) (x : Space K)\n    (hx : x.val ∈ realization (deletion K v)) :\n    collapseHomotopy K u v huv hExt (t, x) = x", DescribeRole.Theorem),
            Node("inclusion-coordinates", "inclusion_coordinates", "inclusion_coordinates",
                "The inclusion has exactly the same coordinate vector on the original finite label type, including ghost coordinates.",
                "theorem inclusion_coordinates (K : PreAbstractSimplicialComplex V) (v : V)\n    (y : Space (deletion K v)) :\n    (realizationInclusion (deletion_le K v) y).val = y.val", DescribeRole.Theorem),
            Node("deletion-coordinate-zero", "deletion_coordinate_zero", "deletion_coordinate_zero",
                "A point of the literal deletion has zero coordinate at the original label v, which remains in V.",
                "theorem deletion_coordinate_zero (K : PreAbstractSimplicialComplex V) (v : V)\n    (y : Space (deletion K v)) : y.val v = 0", DescribeRole.Theorem),
            Node("restricted-coordinate-zero", "restricted_coordinate_zero", "restricted_coordinate_zero",
                "Every point of the actual restricted independence realization has coordinate zero at every label not satisfying the allowed-ground predicate, including excluded ghosts.",
                "theorem restricted_coordinate_zero (G : SimpleGraph V) (p : V → Prop)\n    (x : Space (restricted G p)) (a : V) (ha : ¬ p a) : x.val a = 0", DescribeRole.Theorem),
            Node("graph-extends", "graph_extends", "graph_extends",
                "For actual restricted independence faces, if survivor u is allowed and every allowed neighbor of u is a neighbor of v, adjoining u to a face containing v preserves independence and allowed ground membership. No graph subtype is introduced.",
                "theorem graph_extends (G : SimpleGraph V) (p : V → Prop) (u v : V)\n    (huv : u ≠ v) (hpu : p u)\n    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :\n    Extends (restricted G p) u v", DescribeRole.Theorem),
            Node("restricted-deletion", "restricted_deletion", "restricted_deletion",
                "The literal deletion of v from restricted G p is exactly restricted G (a maps to p a and a not equal to v), on the SAME V.",
                "theorem restricted_deletion (G : SimpleGraph V) (p : V → Prop) (v : V) :\n    deletion (restricted G p) v = restricted G (fun a => p a ∧ a ≠ v)", DescribeRole.Theorem),
            Node("graphsequence", "graphSequence", "graphSequence",
                "Apply the proved extension lemma to construct the genuine original-label elementary certificate for the actual restricted independence complex, with literal deletion endpoint.",
                "def graphSequence (G : SimpleGraph V) (p : V → Prop) (u v : V)\n    (huv : u ≠ v) (hpu : p u)\n    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :\n    Sequence (restricted G p) (deletion (restricted G p) v)", DescribeRole.Definition),
            Node("graphrestrictedsequence", "graphRestrictedSequence", "graphRestrictedSequence",
                "View the same certificate at the exactly equal restriction-excluding-v endpoint, using equality transport only.",
                "def graphRestrictedSequence (G : SimpleGraph V) (p : V → Prop) (u v : V)\n    (huv : u ≠ v) (hpu : p u)\n    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :\n    Sequence (restricted G p) (restricted G (fun a => p a ∧ a ≠ v))", DescribeRole.Definition),
            Node("graphsdr", "graphSDR", "graphSDR",
                "Realize that actual graph certificate through the native relative API, fixing the whole deletion realization. This is not a claim of equality to the existing simultaneous coordinate fold.",
                "def graphSDR (G : SimpleGraph V) (p : V → Prop) (u v : V)\n    (huv : u ≠ v) (hpu : p u)\n    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :\n    RelativeSDR (restricted G p) (deletion (restricted G p) v)\n      (deletion_le (restricted G p) v)", DescribeRole.Definition),
            Node("independencesequence", "independenceSequence", "independenceSequence",
                "For the actual unrestricted independenceComplex of a simple graph, distinct u and v and open-neighborhood containment N(u) subset N(v) yield the original-label elementary deletion certificate.",
                "def independenceSequence (G : SimpleGraph V) (u v : V) (huv : u ≠ v)\n    (hdom : G.neighborSet u ⊆ G.neighborSet v) :\n    Sequence (independenceComplex G).toPreAbstractSimplicialComplex\n      (deletion (independenceComplex G).toPreAbstractSimplicialComplex v)", DescribeRole.Definition),
            Node("independence-deletion", "independence_deletion", "independence_deletion",
                "Deleting v from the actual unrestricted independenceComplex is literally the same complex on V as restricting to labels different from v.",
                "theorem independence_deletion (G : SimpleGraph V) (v : V) :\n    deletion (independenceComplex G).toPreAbstractSimplicialComplex v =\n      restricted G (fun a => a ≠ v)", DescribeRole.Theorem),
            Paragraph(Text("The existing coordinate transfer/foldHomotopy/foldEquiv and forest "
                + "leafEquiv are not re-proved or renamed here. The new content is the actual finite "
                + "elementary Sequence with original-label pair data and literal deletion fixedness. "
                + "The simultaneous fold need not equal the successive pairwise homotopy. "
                + "No universal root-K supplier, unrestricted critical-face construction, sphere "
                + "quotient, disk collar, or attached-cell branch is discharged by this module. "
                + "Kernel and axiom-closure checks, faithful Reg source observation, Scribe coverage, "
                + "all native gates, remote checks, publication and cleanup remain integration work.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose)), Paragraph(Text("Exact attempted Lean contract: " + rawContract))), role);
}
