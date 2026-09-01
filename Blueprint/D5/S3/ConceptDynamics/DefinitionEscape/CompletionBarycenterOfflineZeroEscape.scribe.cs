using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class CompletionBarycenterOfflineZeroEscapeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscape/CompletionBarycenterOfflineZeroEscape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A completion barycenter observer cannot recover squared offline displacement.",
        H("Completion Barycenter Offline-Zero Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-barycenter-offline-zero-escape"),
                DeclarationHandle.Create(
                    Prefix + "completion_barycenter_offline_zero_escape"),
                H("Squared displacement escapes the completion barycenter"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A spectral state is a pair (gamma, delta) whose displacement lies "
                            + "strictly between negative one half and one half. The completion "
                            + "observer reads one half plus i times gamma, whereas the target is "
                            + "the square of delta.")),
                    Paragraph(Text(
                        "The legal states (0, 1/4) and (0, 1/3) both read as one half. Their "
                            + "target values are computed as 1/16 and 1/9, so they form a "
                            + "nonempty target-sensitive observer fiber.")),
                    Paragraph(Text(
                        "The accepted target recovery criterion turns this explicit defect into "
                            + "the stated failure of every real-valued recovery function on "
                            + "complex observations. The proof therefore reuses the repository's "
                            + "general factorization theorem rather than duplicating it.")),
                    Paragraph(Text(
                        "The companion residual theorem applies the accepted residual join law: "
                            + "adjoining the squared displacement itself makes the target defect "
                            + "empty. A positive control computes different observations for "
                            + "(1, 0) and (2, 0), confirming that only the displacement direction "
                            + "is lost in these witnesses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula recover = F.Id("f");
        Formula state = F.Id("x");
        Formula target = F.Id("squareTarget");
        Formula observer = F.Id("completionObserver");

        return Disp(Seq(
            Neg, Sp, Exists, Sp, recover, Colon, Sp,
            F.Id("Complex"), Sp, To, Sp, F.Id("Real"), Comma, Sp,
            Forall, Sp, state, Colon, Sp, F.Id("SpectralState"), Comma, Sp,
            Apply(target, state), Sp, Eq, Sp,
            Apply(recover, Apply(observer, state)), Dot));
    }
}
