using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class TrisectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/Trisection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact coefficient extraction separates all three residue classes at every natural index over any commutative ring.", H("Trisection"), Blocks(
            Paragraph(Text("Exact coefficient extraction separates all three residue classes at every natural index over any commutative ring.")),
            Node("0", "coeff_shift_expand_three", "Coeff shift expand three.", DescribeRole.Theorem),
            Node("1", "coeff_three_components", "A formal dissection determines each progression at every natural degree.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. This generic coefficient argument uses the pinned Mathlib power-series APIs and has no assumed analytic convergence or cubic theta identity. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("trisection-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
