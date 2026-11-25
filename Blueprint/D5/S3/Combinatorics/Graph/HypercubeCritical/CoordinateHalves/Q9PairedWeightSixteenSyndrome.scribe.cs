using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9PairedWeightSixteenSyndromeDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedWeightSixteenSyndrome";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The syndrome is an affine cube on four pairs.",
        H("The syndrome is an affine cube on four pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-syndrome-affine"),
                DeclarationHandle.Create(Module + ".pairedSyndrome_affine"),
                H("The syndrome is an affine cube on four pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Translations that flip both bits in a coordinate pair preserve all four pair parities. Their action is transitive on this syndrome. The twelve dimer sites have exactly these sixteen odd adjacency rows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relabeled-syndrome-ne-one-exchange"),
                DeclarationHandle.Create(Module + ".relabeled_syndrome_ne_one_exchange"),
                H("The paired syndrome lies outside every one-exchange orbit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An exchange from a binary kernel word produces the symmetric difference of two open shells. At weight sixteen the shells are disjoint and each site has at least seven distance-two neighbors in the support. The paired syndrome has distance-two degree four. Translations and coordinate permutations preserve this degree."))),
                DescribeRole.Theorem)),
        []));
}
