using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class ModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Model", H("Model"),
        Blocks(
            Paragraph(Text("L¹ (Feichtinger) space of vacuum coefficients, Heisenberg representation, reproducing formula, Schur's lemma.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/Model.integral_form_eq_mul_modelInner"),
                H("integral_form_eq_mul_modelInner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Uniqueness of the invariant form: if B_z are bounded sesquilinear forms on the reproducing space, z ↦ B_z(v,w) is integrable and ∫B_z dν is invariant under all ρ(x), then ∫B_z(v,w) dν = (∫B_z(vac,vac) dν)·⟨v,w⟩.")))))));
}
