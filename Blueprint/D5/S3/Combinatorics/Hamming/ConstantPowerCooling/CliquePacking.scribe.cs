using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming.ConstantPowerCooling;

internal sealed class CliquePackingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/ConstantPowerCooling/CliquePacking.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degrees and incidences count a packing of fixed-size cliques.",
        H("Degrees in a clique packing"),
        Blocks(
            Describe.Lean(DescribeId.Create("packing-degree"),
                DeclarationHandle.Create(Prefix + "packedGraph_degree"),
                H("Degrees in a clique packing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("For a finite indexed family of k-element blocks in which distinct blocks meet in at most one point, the degree of any point in the graph of covered pairs is (k − 1) times the number of blocks through it. The other points in the blocks through a point form pairwise disjoint neighbor sets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incidence-sum"),
                DeclarationHandle.Create(Prefix + "incidence_sum"),
                H("Total block incidence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("For a finite indexed family of k-element blocks on a finite set, the sum of the numbers of incident blocks over points is k times the number of blocks. The two sums count the same point–block incidences."))), DescribeRole.Theorem)),
        []));
}
