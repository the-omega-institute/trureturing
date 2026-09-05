using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class CanonicalZeroDataProviderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/CanonicalZeroDataProvider."
            + "canonical_zeroSum_eq";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Package an actual exhaustive zeta-zero enumeration and prove canonicality for permutation-invariant zero sums.",
            H("Canonical ZeroData Provider"),
            Blocks(Describe.Lean(
                DescribeId.Create("canonical-zero-sum-agrees-with-every-exhaustive-enumeration"),
                DeclarationHandle.Create(Declaration),
                H("Canonicality at the observable level"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("zeroSum", F.Id("canonicalZeroData(S)")), Sp, Eq, Sp,
                    Call("zeroSum", F.Id("Z"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The provider is selected by classical choice from a proof that the actual "
                            + "nontrivial zeta-zero set is infinite. It is exhaustive, duplicate-free, "
                            + "multiplicity-aware, reflection faithful, conjugation faithful, and "
                            + "locally finite.")),
                    Paragraph(Text(
                        "The ordering is not asserted to be intrinsic. Existing enumeration-invariance "
                            + "theorems show that finite symmetric sums, convergence, and zero-sum "
                            + "values agree with every other valid ZeroData enumeration."))),
                DescribeRole.Theorem))));
    }
}
