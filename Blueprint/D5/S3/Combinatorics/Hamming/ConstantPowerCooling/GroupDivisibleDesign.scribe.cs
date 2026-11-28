using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming.ConstantPowerCooling;

internal sealed class GroupDivisibleDesignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supplied uniform group divisible design attains the finite upper bound.",
        H("Optimality from a finite design"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-optimum"),
                DeclarationHandle.Create(Prefix + "finite_cpecc_support_optimum_of_design"),
                H("Optimality from a finite design"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("Under the finite upper bound's hypotheses on n, w, t, g and k, supply a k-group divisible design on V with groups of size g. Then n(n − g)/(k(k − 1)) is the greatest attainable number of information classes. Each block supplies one class consisting of its w-subsets. It has enough points to avoid any deletion of t points, and distinct blocks share at most one point. Counting incidences in the graph of cross-group pairs gives exactly the required number of blocks."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-design"),
                DeclarationHandle.Create(Prefix + "GroupDivisibleDesign"),
                H("A uniform group divisible design"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("The groups on a point set V are equivalence classes of a setoid, each of size g. The blocks form a finite family of k-subsets. A distinct pair in one group belongs to no block, and each cross-group pair belongs to exactly one block. For a finite point set of size n this is a design of type g raised to the number of groups."))), DescribeRole.Definition)),
        []));
}
