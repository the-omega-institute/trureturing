using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ZeroDataSemanticNonvacuityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/ZeroDataSemanticNonvacuity."
            + "realized_claim_with_nontrivial_zero";

    public DocumentDefinition Create()
    {
        Formula zeroData = F.Id("ZeroData");
        Formula predicate = F.Id("P");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Separate outer universal vacuity from claims realized on an actual zeta-zero enumeration.",
            H("Semantic Nonvacuity for ZeroData"),
            Blocks(Describe.Lean(
                DescribeId.Create("zero-data-universal-claim-realized-with-an-actual-zero"),
                DeclarationHandle.Create(Declaration),
                H("Universal claims acquire a real witness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RiemannVonMangoldt", F.Id("zetaZeroConfig")), Sp, And, Sp,
                    Call("Forall", zeroData, predicate), Sp, Implies, Sp,
                    Call("Exists", zeroData, Seq(predicate, Sp, And, Sp,
                        Call("ExistsNontrivialZero", F.Id("rho"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every supplied ZeroData is indexed by the natural numbers and therefore "
                            + "already contains a zeroth represented zero. The possible vacuity is "
                            + "the emptiness of the outer type ZeroData itself.")),
                    Paragraph(Text(
                        "Riemann-von Mangoldt growth supplies Nonempty ZeroData through the existing "
                            + "infinitude equivalence. A universally quantified theorem can then be "
                            + "instantiated on the selected exhaustive enumeration and on an actual "
                            + "represented nontrivial zeta zero."))),
                DescribeRole.Theorem))));
    }
}
