using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Mass;

internal sealed class TorusMajorantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Torus Majorant", H("Torus Majorant"),
        Blocks(
            Paragraph(Text("Scaled inverse different in self-adjoint finite adeles is a compact open subgroup. Hermitian Gauss sums integrable over characters, bounded by a zeta value. Integrable logarithmic majorant on a complex torus; principal ideles are discrete.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Mass/TorusMajorant.integrable_prod_inv_one_add_log_sq"),
                H("integrable_prod_inv_one_add_log_sq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The function a ↦ ∏_x (1 + (log |a_x|)²)⁻¹ is integrable for Haar measure on (ℂ^×)^ι, ι finite.")))))));
}
