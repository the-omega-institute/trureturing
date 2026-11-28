using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class BaseChangeEigencharDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Change Eigenchar", H("Base Change Eigenchar"),
        Blocks(
            Paragraph(Text("Twisted trace over E' is proportional to trace over E for matching functions. Existence of weak prime-degree base change for definite unitary groups with matched local data. Base change keeps a pro-p Iwahori eigencharacter, composed with the norm.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar.exists_baseChange_isIwahoriEigen"),
                H("exists_baseChange_isIwahoriEigen"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Base change along a step E'/E with compatible CM types, at a split w with μ_w = 1 and one split place u above: if f has eigencharacter ξ at w, some eigenform f' over E' matches f off w (IsWeakBaseChange) with eigencharacter ξ∘Nm at u.")))))));
}
