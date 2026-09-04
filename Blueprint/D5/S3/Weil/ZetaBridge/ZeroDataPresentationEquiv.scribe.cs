using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ZeroDataPresentationEquivDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Weil/ZetaBridge/ZeroDataPresentationEquiv.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exhaustive ZeroData presentations admit a unique zero-preserving symmetry-equivariant reindexing.",
            H("Canonical equivalence of ZeroData presentations"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("zero-data-presentation-equivalence-unique"),
                    DeclarationHandle.Create(Module + "zeroDataPresentationEquiv_unique"),
                    H("Zero-preserving reindexing is unique"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("Z'.zero(e(n)) = Z.zero(n)"), Sp, Implies, Sp,
                        F.Id("e = zeroDataPresentationEquiv(Z,Z')")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The construction reuses the existing equivalence from each ZeroData presentation to the canonical nontrivial-zero subtype."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zero-data-presentation-mirror-equivariance"),
                    DeclarationHandle.Create(Module + "zeroDataPresentationEquiv_mirror"),
                    H("Presentation transport intertwines the mirror"),
                    StatementSource.FromAuthor(Disp(F.Id("e(M_Z(n)) = M_Z'(e(n))"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Reflection, conjugation, multiplicity, and the same-height mirror are transported by the unique reindexing."))),
                    DescribeRole.Theorem))));
    }
}
