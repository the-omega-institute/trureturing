using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class CanonicalZeroDataNonvacuityAssemblyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/CanonicalZeroDataNonvacuityAssembly."
            + "canonical_zeroData_closed_chain";

    public DocumentDefinition Create()
    {
        Formula zeroSet = F.Id("{rho | IsNontrivialZero rho}");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Assemble Riemann-von Mangoldt growth into a faithful, exhaustive, nonvacuous ZeroData certificate.",
            H("Closed Canonical ZeroData Nonvacuity Chain"),
            Blocks(Describe.Lean(
                DescribeId.Create("riemann-von-mangoldt-closes-the-zero-data-nonvacuity-chain"),
                DeclarationHandle.Create(Declaration),
                H("Count growth to semantic realization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RiemannVonMangoldt", F.Id("zetaZeroConfig")), Sp, Implies, Sp,
                    Call("Infinite", zeroSet), Sp, And, Sp,
                    Call("Nonempty", F.Id("ZeroData")), Sp, And, Sp,
                    Call("Exists", F.Id("CanonicalZeroDataCertificate"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The certificate contains an actual ZeroData value, exact representation of "
                            + "every nontrivial zeta zero by a unique index, positive analytic "
                            + "multiplicity, faithful reflection and conjugation, and finite symmetric "
                            + "spectral cutoffs.")),
                    Paragraph(Text(
                        "The chain is logically closed downstream of the explicit canonical "
                            + "Riemann-von Mangoldt source. A hypothesis-free provider requires the "
                            + "global Riemann-von Mangoldt assembly to be admitted separately."))),
                DescribeRole.Theorem))));
    }
}
