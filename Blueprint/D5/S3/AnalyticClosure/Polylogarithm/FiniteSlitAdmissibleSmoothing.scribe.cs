using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;
internal sealed class FiniteSlitAdmissibleSmoothingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original admissible coefficients have every fixed positive smoothing sign and strict binomial excess.",
        H("FiniteSlitAdmissibleSmoothing"), Blocks(
            Describe.Lean(DescribeId.Create("admissible-smoothing"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every fixed smoothing order for admissible compositions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("For every positive head greater than one, arbitrary positive-entry tail, positive ell and fixed j>=1, the original ordinary coefficients of (1-z)^(-j) times F(z)^(-ell) eventually are strictly positive and exceed zeta(head,tail)^(-ell) times choose(n+j-1,n). The existing ordinary inverse and endpoint results retain the strict-largest-index convention, removable origin and derivative divided by n factorial.")),
                    Paragraph(Text("The first excess is exactly the first ordinary partial sum minus the actual endpoint. Its radial HasSum is proved by the public Cauchy product with the geometric series and subtraction of the endpoint geometric series. The quantitative admissible radial result discharges the positive margin. The generic signed-prefix Abel theorem then yields every fixed j while keeping the entire finite prefix.")),
                    Paragraph(Text("This is the admissible branch of the original event. Leading head equal to one still requires its actual log-growth and normalized reciprocal radial margin. The full all-composition problem is not claimed solved; thresholds remain dependent on the fixed parameters."))),
                DescribeRole.Theorem))));
}
