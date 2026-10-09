using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite subset of the edges incident to the vertex has a distinct sum of labels.",
        H("Additively rigid vertex"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubicargraphdefs-isarvertex"),
                DeclarationHandle.Create(Prefix + "IsARVertex"),
                H("Additively rigid vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite subset of the edges incident to the vertex has a distinct sum of labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubicargraphdefs-isargraph"),
                DeclarationHandle.Create(Prefix + "IsARGraph"),
                H("Exact interval edge labeling"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The edge labels form a bijection onto the integers from one to the edge count, and every vertex is additively rigid."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubicargraphdefs-ar_vertex_of_no_additive_relation"),
                DeclarationHandle.Create(Prefix + "ar_vertex_of_no_additive_relation"),
                H("Cubic local criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive distinct labels on a degree-three vertex give distinct subset sums whenever no two incident labels sum to the third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubicargraphdefs-cubic_card_identity"),
                DeclarationHandle.Create(Prefix + "cubic_card_identity"),
                H("Cubic degree-sum identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three times the vertex count is twice the edge count by the degree-sum formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubicargraphdefs-cubic_order_constraints"),
                DeclarationHandle.Create(Prefix + "cubic_order_constraints"),
                H("Small orders and parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonempty simple cubic graph has at least four vertices and its vertex count is even."))),
                DescribeRole.Theorem))));
}
