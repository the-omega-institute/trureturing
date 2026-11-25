using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.Waring;

internal sealed class WaringCoeffBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounds for divided difference coefficients",
        H("Bounds for divided difference coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coeffbound"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffCoeff_bound"),
                H("Bounds for divided difference coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("For shifts bounded by N, each divided difference coefficient below degree d is bounded by the original coefficient bound times a binomial sum and N to the corresponding reduced degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyldiff"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/Waring/WaringCoeffBound.diffH_polyEval"),
                H("Polynomial finite differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Semigroups/waringformalization2026lean")),
                Blocks(Paragraph(Text("The step-h difference of an integer polynomial is h times the polynomial with the divided difference coefficients."))),
                DescribeRole.Theorem)
        )));
}
