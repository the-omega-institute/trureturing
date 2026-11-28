using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class BaseChangeLabelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Change Label", H("Base Change Label"),
        Blocks(
            Paragraph(Text("Base change keeps a depth-zero label at an inert place via Shintani lift.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLabel.exists_baseChange_hasLabel"),
                H("exists_baseChange_hasLabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Take a step E'/E, w split with μ_w = 1, u split the only place above w, of residue degree [E':E]. If f has as label a character Ξ with lift Ξ' (Lift over ℕ), some eigenform over E', a weak base change of f off w, has label Ξ' at u.")))))));
}
