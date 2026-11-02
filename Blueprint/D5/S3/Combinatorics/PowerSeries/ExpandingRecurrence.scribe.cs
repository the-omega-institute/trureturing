using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class ExpandingRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/ExpandingRecurrence.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A homogeneous positive-degree expanding recurrence has only the zero formal power series solution over any commutative ring.", H("ExpandingRecurrence"), Blocks(
            Paragraph(Text("A homogeneous positive-degree expanding recurrence has only the zero formal power series solution over any commutative ring.")),
            Node("0", "eq_zero_of_mul_eq_X_expand", "Every coefficient of a homogeneous expanding recurrence vanishes over any commutative ring.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. This generic coefficient argument uses the pinned Mathlib power-series APIs and has no assumed analytic convergence or cubic theta identity. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("expandingrecurrence-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
