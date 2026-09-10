using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RationalIntervalExpressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational arithmetic checks provide proof inputs for real analytic covers.",
        H("Rational Interval Expression Certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-interval-expression-expr"),
                DeclarationHandle.Create("D5/S0/Certificates/RationalIntervalExpression.Expr"),
                H("Arithmetic expression with proposed endpoints"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The syntax stores rational annotations while the underlying expression retains real semantics."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-interval-expression-bounds"),
                DeclarationHandle.Create("D5/S0/Certificates/RationalIntervalExpression.bounds"),
                H("Proposed rational bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This projection has no truth authority by itself. The check validates it."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-interval-expression-value"),
                DeclarationHandle.Create("D5/S0/Certificates/RationalIntervalExpression.value"),
                H("Real evaluation independent of annotations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation discards every endpoint and applies the actual real field operations."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-interval-expression-check"),
                DeclarationHandle.Create("D5/S0/Certificates/RationalIntervalExpression.check"),
                H("Exact local rational checks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All four multiplication corners, square sign cases and strict reciprocal guards are checked recursively."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-interval-expression-checked-expression-encloses"),
                DeclarationHandle.Create("D5/S0/Certificates/RationalIntervalExpression.checked_expression_encloses"),
                H("Successful checks enclose every real input"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Structural induction proves a real enclosure from only exact rational local comparisons and membership in the input box. No enclosure oracle, external PASS or rational-only input restriction is assumed."))), DescribeRole.Theorem))));
}
