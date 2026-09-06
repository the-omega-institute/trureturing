using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RiemannVonMangoldtCountGrowthDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/RiemannVonMangoldtCountGrowth."
            + "dyadic_zero_count_tendsto_atTop";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Riemann-von Mangoldt growth forces the multiplicity-weighted dyadic zero count to diverge.",
            H("Riemann–von Mangoldt Zero-Count Growth"),
            Blocks(Describe.Lean(
                DescribeId.Create("riemann-von-mangoldt-forces-dyadic-zero-count-growth"),
                DeclarationHandle.Create(Declaration),
                H("Dyadic zero counts tend to infinity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RiemannVonMangoldt", F.Id("Z")), Sp, Implies, Sp,
                    Call("Tendsto", F.Id("N_Z(T,2T)"), F.Id("atTop"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof extracts the exact dyadic main term and logarithmic error from "
                            + "the repository's RiemannVonMangoldt structure, then proves the main "
                            + "term eventually dominates the error.")),
                    Paragraph(Text(
                        "This is the quantitative source used to force infinitude of the canonical "
                            + "nontrivial-zeta-zero carrier."))),
                DescribeRole.Theorem))));
    }
}
