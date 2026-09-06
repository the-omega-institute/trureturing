using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class CompleteRootSupergraphExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exhaustive common-unbiased projector catalogue with a single canonical six-block "
        + "and a disjoint bipartite remainder excludes two mutually unbiased completions.",
        H("Complete Root Supergraph Exclusion"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-root-supergraph-excludes-double-completion"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion."
                + "no_mutually_unbiased_completions_of_complete_root_supergraph"),
            H("Exhaustive coverage and a one-sided graph certificate exclude a quartet"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("CompleteRootCover"), Sp, Land, Sp,
                F.Id("CanonicalSixBlockAndBipartiteRemainder"), Sp,
                Rightarrow, Sp, F.Id("NoMutuallyUnbiasedCompletionPair"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Lean statement is on the existing RankOneContext and overlap API. "
                    + "An arbitrary label type indexes candidate projectors. Every projector of "
                    + "each actual completion must equal a labelled candidate. Any distinct labels "
                    + "with zero trace overlap either both lie in a six-element canonical set, "
                    + "or both lie outside it and have opposite Boolean colors. The contexts "
                    + "are complete orthogonal six-element rank-one measurements.")),
                Paragraph(Text(
                    "Three distinct vertices cannot form a clique in a bipartite component. "
                    + "Therefore every six-element context uses exactly the canonical set. "
                    + "Two such contexts share a normalized rank-one projector, giving overlap "
                    + "one, which contradicts mutual unbiasedness at overlap one-sixth.")),
                Paragraph(Text(
                    "Only a supergraph is required; allowed edges may disappear under parameter "
                    + "variation. The theorem does not read or trust an external interval report. "
                    + "A separate analytic, kernel-checked adapter must discharge exhaustive "
                    + "root coverage and the certified nonedge implications. No intrinsic "
                    + "information score or maximal-catalog admission is asserted here."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("root-tube-cover-forces-large-cross-overlap"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion."
                    + "six_frames_have_large_cross_overlap_of_root_tube_cover"),
                H("Two covered six-frames have a quantitatively large cross overlap"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("TubeCoverWithLargeSameTubeOverlap"), Sp, Land, Sp,
                    F.Id("CanonicalSixBlockAndBipartiteSmallOverlapSupergraph"), Sp, Land, Sp,
                    F.Id("TwoSixFramesWithSmallInternalOverlaps"), Sp, Rightarrow, Sp,
                    F.Id("SomeCrossOverlapAtLeastMu"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Tubes are sets of matrices on the existing Fin 6 carrier. "
                        + "For eta <= mu, any two matrices in one tube have real trace overlap "
                        + "at least mu. Matrices in distinct tubes with overlap below eta must "
                        + "have labels in the canonical six-block, or labels of opposite colors "
                        + "in the disjoint bipartite remainder. Every member of both six-frames "
                        + "lies in a tube, and all within-frame overlaps are below eta.")),
                    Paragraph(Text(
                        "Each frame has distinct labels by the same-tube lower bound. "
                        + "The existing private clique argument confines both label sets to "
                        + "the six canonical labels. The frames therefore share a label, and "
                        + "the same-tube bound supplies a cross overlap at least mu. "
                        + "Tubes may be empty, contain several roots, or overlap. "
                        + "Root existence, uniqueness, and exact root count are not needed.")),
                    Paragraph(Text(
                        "For normalized outer products, this is a squared-inner-product "
                        + "bound. The interval instance uses mu=99/100 and eta=1/100000000; "
                        + "the theorem itself does not read that instance or its PASS report. "
                        + "The previous exact root-catalogue theorem is retained. "
                        + "No new semantic Arena or intrinsic-information gain is asserted."))),
                DescribeRole.Theorem))));
}
