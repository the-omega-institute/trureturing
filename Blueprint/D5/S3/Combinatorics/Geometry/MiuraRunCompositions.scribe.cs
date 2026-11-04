using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraRunCompositionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraRunCompositions.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive run lengths are actual indexed integer vectors.", H("Exact frozen-run length counts"),
        Blocks(
            Describe.Lean(DescribeId.Create("miura-positive-lengths"),
                DeclarationHandle.Create(Prefix + "PositiveLengths"), H("Positive indexed lengths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural N and r, a length vector assigns a positive natural number to every index in Fin r, and the sum of all entries is N."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miura-remove-ones"),
                DeclarationHandle.Create(Prefix + "removeOnesEquiv"), H("Remove the compulsory cell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If r is at most N, subtracting one from every run length gives a bijection with nonnegative indexed vectors of total N-r. The inverse adds one to every entry."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miura-positive-lengths-card"),
                DeclarationHandle.Create(Prefix + "positive_lengths_card"), H("The exact binomial cardinality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every N and r with 1 at most r at most N, the actual positive indexed length vectors are counted by choose(N-1,r-1). The bijection removing one cell per run is composed with the pinned symmetric-power equivalence and its stars-and-bars cardinality. For frozen rows or columns, N is the available number of unoccupied positions and r is the number of maximal frozen runs."))), DescribeRole.Theorem))));
}
