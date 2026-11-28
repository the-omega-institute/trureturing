using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class AdaptedSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adapted Splitting", H("Adapted Splitting"),
        Blocks(
            Paragraph(Text("Zero term along an isotropic subspace taken in stages; independent of the frame. Witt decomposition: every isotropic frame splits off hyperbolic planes plus a framed complement. Adapted splittings; the standard splitting of a space plus hyperbolic planes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/AdaptedSplitting.exists_splitting"),
                H("exists_splitting"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every q×p matrix k over E with a left inverse and k*Jk = 0, J the Gram matrix of V, is the isotropic frame k of a splitting of V over some space V₀.")))))));
}
