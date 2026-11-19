using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowLiteralUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal six-row purity upper bound and exact original ordered equality", H("SixRowLiteralUpper"), Blocks(
            Describe.Lean(DescribeId.Create("sixrowliteralupper-literal-upper-and-equality"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.literal_upper_and_equality"),
                H("ordered literal upper bound and equality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least 23, an antitone nonnegative unit-mass spectrum l with APPT of its actual e-labelled diagonal has sum l_i squared at most theta(n), with equality iff the entire original l equals centralSpectrum(n). Extraction and concentration use identical original boundary moments. Equality is conditional on the stated premises; no concentrated vector is assumed APPT."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowliteralupper-density-upper"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper.density_upper"),
                H("arbitrary APPT density upper bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least 23 and an arbitrary PSD trace-one APPT complex matrix on Fin 6 times Fin n, the real trace of its square is at most theta(n): 6/(35n) for even n and 6(35n+2)/(35n+1)^2 for odd n. The existing spectral reduction yields one ordered spectrum, APPT of its labelled diagonal and the equality of purities used for the transfer."))), DescribeRole.Theorem)
        )));
}
