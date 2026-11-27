using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Unramified;

internal sealed class UniformiserScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformiser Scalar", H("Uniformiser Scalar"),
        Blocks(
            Paragraph(Text("Scalar by which a uniformiser acts in the Weil representation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Unramified/UniformiserScalar.frobValue"),
                H("frobValue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The complex number χ(ϖ_w)·q_w^{k/2}, where χ = AutChar.spaceChar a k is the Hecke character x ↦ a(x/x̄)υ(x)^{−k} and ϖ_w the chosen uniformiser at w.")))))));
}
