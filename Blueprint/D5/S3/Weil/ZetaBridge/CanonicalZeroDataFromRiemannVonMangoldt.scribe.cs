using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class CanonicalZeroDataFromRiemannVonMangoldtDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/CanonicalZeroDataFromRiemannVonMangoldt."
            + "nonempty_zeroData_of_riemannVonMangoldt";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Riemann-von Mangoldt count growth supplies an actual exhaustive ZeroData enumeration.",
            H("Canonical ZeroData from Riemann–von Mangoldt"),
            Blocks(Describe.Lean(
                DescribeId.Create("riemann-von-mangoldt-supplies-nonempty-zero-data"),
                DeclarationHandle.Create(Declaration),
                H("Canonical nonvacuity source"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RiemannVonMangoldt", F.Id("zetaZeroConfig")), Sp, Implies, Sp,
                    Call("Nonempty", F.Id("ZeroData"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Unbounded dyadic zero counts force the canonical set-level zeta-zero "
                            + "carrier to be infinite. The existing exact equivalence between "
                            + "zero-set infinitude and Nonempty ZeroData then supplies the inhabitant.")),
                    Paragraph(Text(
                        "Enumeration, analytic multiplicity, symmetry permutations, and local "
                            + "finiteness are reused from the established equivalence rather than "
                            + "reconstructed in this module."))),
                DescribeRole.Theorem))));
    }
}
