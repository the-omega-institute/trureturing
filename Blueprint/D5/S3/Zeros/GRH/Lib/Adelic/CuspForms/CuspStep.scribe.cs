using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class CuspStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cusp Step", H("Cusp Step"),
        Blocks(
            Paragraph(Text("Parametrisation and product rule of the unipotent radical; norm bounds for integral matrices. Deep in the cusp a cuspidal function is bounded by its oscillation, explicit depth.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/CuspStep.norm_le_of_firstMinimum_lt"),
                H("norm_le_of_firstMinimum_lt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let F be a form of level K(M), its type a cusp kernel, N ≠ 0 in the different, κ = cuspConst, 0 < δ ≤ 1, λ(g) < (δ/(Mκ²))ⁿ. If |F(gx) − F(g)| ≤ C for real x with all ‖x_w − 1‖ ≤ δ, then |F(g)| ≤ C.")))))));
}
