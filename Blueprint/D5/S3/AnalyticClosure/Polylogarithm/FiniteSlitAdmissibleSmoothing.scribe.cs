using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;
internal sealed class FiniteSlitAdmissibleSmoothingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original coefficients have the full all-composition eventual signs and strict admissible binomial excess.",
        H("FiniteSlitAdmissibleSmoothing"), Blocks(
            Describe.Lean(DescribeId.Create("admissible-smoothing"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every fixed smoothing order for admissible compositions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("For every positive head greater than one, arbitrary positive-entry tail, positive ell and fixed j>=1, the original ordinary coefficients of (1-z)^(-j) times F(z)^(-ell) eventually are strictly positive and exceed zeta(head,tail)^(-ell) times choose(n+j-1,n). The existing ordinary inverse and endpoint results retain the strict-largest-index convention, removable origin and derivative divided by n factorial.")),
                    Paragraph(Text("The first excess is exactly the first ordinary partial sum minus the actual endpoint. Its radial HasSum is proved by the public Cauchy product with the geometric series and subtraction of the endpoint geometric series. The quantitative admissible radial result discharges the positive margin. The generic signed-prefix Abel theorem then yields every fixed j while keeping the entire finite prefix.")),
                    Paragraph(Text("The admissible interface supplies the strict baseline in the full all-composition theorem. Thresholds depend on the fixed composition, reciprocal power and smoothing order."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-eventual-signs"),
                DeclarationHandle.Create(Prefix + "full_result"),
                H("Every positive composition and fixed smoothing order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("For every positive head, every finite positive-entry tail including the empty tail, and every positive ell, the original ordinary inverse coefficients are eventually strictly negative. For each further fixed j>=1 the original coefficients of (1-z)^(-j) times F(z)^(-ell) are eventually strictly positive. If the head exceeds one, they also strictly exceed zeta(head,tail)^(-ell) times choose(n+j-1,n). These are the strict-largest-index source coefficients, with the removable nonzero origin and no extra factorial.")),
                    Paragraph(Text("For head one the original remainder dichotomy is applied to its proved controls, and its exact composition identity feeds the existing logarithmic norm bound. Along w=1-r in the positive real slit ray, source agreement and the positive source series identify the actual continued value as r^depth times a positive real normalized value x. Raising its norm bound to ell retains r^(depth*ell). The existing slit logarithmic decay makes the upper majorant times 1-r smaller than this numerator eventually, proving x^ell times 1-r<=1 and hence a radial reciprocal margin of one.")),
                    Paragraph(Text("The original endpoint is zero in this branch. The existing all-head first-excess HasSum and the signed-prefix smoothing theorem therefore supply every fixed positive j. The admissible result supplies the other branch and its strict baseline. The result asserts parameter-dependent eventual thresholds; it supplies neither effective nor uniform thresholds, coefficient asymptotic equivalents, or a claim of literature priority."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("xu-zhao-trivariate-cauchy-coefficient-signs"),
                    ResolutionKind.Proved)))));
}
