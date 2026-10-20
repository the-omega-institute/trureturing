using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class MomentCompressionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-moment compression and separately polynomial averages.",
        H("Fourth-moment compression"), Blocks(
            Describe.Lean(DescribeId.Create("nk-moment-index"),
                DeclarationHandle.Create(Owner + "Monomial"),
                H("Monomial coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index set consists of unordered multisets of four optional coordinate indices. Its cardinality is choose(k+4,4), including the constant monomial and every total degree up to four."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nk-moment-0"),
                DeclarationHandle.Create(Owner + "monomial"),
                H("Padded monomial evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A multiset of four optional coordinates represents a monomial of degree at most four. A missing coordinate contributes one. Every lower degree is included by padding with missing coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nk-moment-1"),
                DeclarationHandle.Create(Owner + "nodeCount"),
                H("A fixed node count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k variables the fourth-degree feature space has choose(k+4,4) coordinates. One additional node suffices for every convex combination in this feature space."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nk-moment-2"),
                DeclarationHandle.Create(Owner + "quartic"),
                H("Fourth-degree polynomials"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coefficient vectors on the padded monomial indices represent real polynomials of total degree at most four."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nk-moment-3"),
                DeclarationHandle.Create(Owner + "exists_moment_compression"),
                H("Fixed-size moment compression"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonempty finite family of real k-dimensional points there are exactly choose(k+4,4)+1 nodes taken from that family and nonnegative weights of sum one preserving every monomial average through total degree four. Caratheodory reduction supplies the nodes, and zero weights pad a shorter representation. The nodes therefore stay in every set containing the original family."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nk-moment-4"),
                DeclarationHandle.Create(Owner + "quartic_average_eq"),
                H("Polynomial averages"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of the monomial averages implies equality of the average of every polynomial represented by a coefficient vector on these indices. Finite sums commute and each monomial equality applies separately."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nk-moment-5"),
                DeclarationHandle.Create(Owner + "product_average_eq"),
                H("Separately fourth-degree double averages"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Moment equality preserves the double average of every finite sum of products f(x)g(y), where each factor is a polynomial of degree at most four. This includes total degree eight across the two arguments. The double average factors into the product of the two single averages before the moment identities are applied."))),
                DescribeRole.Theorem))));
}
