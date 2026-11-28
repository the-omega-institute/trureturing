using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal;

internal sealed class LabelCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label Compatibility", H("Label Compatibility"),
        Blocks(
            Paragraph(Text("Compatibility on inertia for squarefree depth-zero types induced with characters of the determinant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility.isLabelledAt"),
                H("isLabelledAt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let r be attached to an eigenform f (standard space, Weil data) with label c, χ_l, t_l at split w, T injective. Above w, r has finite type, the jumps of κ, and IsLabelledAt holds for c∏(X − x_{χ_l})^{t_l}, with determinants away from ℓ.")))))));
}
