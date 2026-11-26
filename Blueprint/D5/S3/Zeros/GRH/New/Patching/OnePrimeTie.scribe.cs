using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Patching;

internal sealed class OnePrimeTieDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Prime Tie", H("One Prime Tie"),
        Blocks(
            Paragraph(Text("Tie at each new prime; top coefficient of Ribet's element clears the projection's denominator.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Patching/OnePrimeTie.exists_diagOp_mem_ellIntegralForms"),
                H("exists_diagOp_mem_ellIntegralForms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Given the string condition, the divisibility of ℓ^ν and Ribet's element with v(md) ≤ γ, some eigenvalues s have v(m s(π)) ≤ γ and make c·s(y) integral for base forms y supported on 𝓧 agreeing with an integral base form where p(b) ≠ 0.")))))));
}
