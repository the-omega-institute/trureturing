using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilGammaResidualEndpointDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Gamma endpoint logarithm admits a complete squared-tail bound, with integrability proved before use in a physical residual certificate.",
        H("Gamma Residual Endpoint"),
        Blocks(
            Describe.Lean(DescribeId.Create("gamma-endpoint-log-bound"),
                DeclarationHandle.Create(Owner + "gamma_endpoint_log_bound"),
                H("Actual singular logarithm and local endpoint distance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<t<=1 and d>=t, prove |log(1-exp(-d))|<=1-log(t). The exponential tangent inequality gives t*exp(-t)<=1-exp(-t); positivity and logarithm monotonicity prove the bound. The singular coefficient is not suppressed and no finite endpoint value is substituted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-affine-square-tail"),
                DeclarationHandle.Create(Owner + "exponential_affine_square_tail"),
                H("Complete square-envelope integral"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real A,B,T, prove both integrability on (T,infinity) and the exact integral of exp(-x)*(A+B*x)^2. An explicit differentiated primitive and the existing polynomial-times-exponential decay give the improper integral. All mixed terms and the infinite integration range remain present."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-logarithmic-endpoint-tail"),
                DeclarationHandle.Create(Owner + "gamma_logarithmic_endpoint_tail"),
                H("Actual endpoint expression has a certified finite squared mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let f,g be measurable complex coefficient functions and distance a measurable real function. On x>T>=0 assume norms of f and g bounded by nonnegative A,B and distance(x)>=exp(-x). For the actual expression R=f+log(1-exp(-distance))*g, prove integrability of exp(-x)*norm(R)^2 and its explicit full tail upper bound. The preceding singular logarithm estimate is substituted before the square and all cross terms are retained.")),
                    Paragraph(Text("The executable consumer evaluates the entire same-window Gamma, Sp, prime, pole and fixed-Rayleigh residual of the genuine prolate model. It uses dyadic endpoint strips, these logarithmic envelopes, and directed Taylor integration with a complex-disc Cauchy remainder. The physical t=exp(-x) substitution, original Gamma realization and piecewise-C1 graph-error bound remain separately documented paper bridges. Lean elaboration, transitive axiom checking and Scribe emission were not executed. The source does not prove a small residual/gap or an all-scale Xi limit."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed"))]));
}
