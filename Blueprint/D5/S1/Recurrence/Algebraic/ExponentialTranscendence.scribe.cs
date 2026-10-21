using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ExponentialTranscendenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ExponentialTranscendence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The formal variable and its exponential satisfy no nonzero rational polynomial relation.",
        H("Polynomial Independence of the Formal Exponential"),
        Blocks(
            Paragraph(Text("Work in the ring Q[[X]] of formal power series. "
                + "Write E=sum over n>=0 of X^n/n!. The expression p(X,E) is defined "
                + "for every bivariate polynomial p with rational coefficients; "
                + "no analytic convergence or substitution of an infinite series with "
                + "nonzero constant coefficient is required.")),
            Node("exponentialEval", "Bivariate evaluation",
                "View Q[t,u] as polynomials in u with coefficients in Q[t]. "
                + "The homomorphism exponentialEval first includes each coefficient "
                + "polynomial in Q[[X]] by t=X, then evaluates u at E.",
                DescribeRole.Definition),
            Node("exponentialEval_injective", "Injectivity of exponential evaluation",
                "The homomorphism p(t,u) -> p(X,E) is injective. Equivalently, "
                + "if sum_j p_j(X)E^j=0 for finitely many rational polynomials p_j, "
                + "then every p_j is zero. Let D be formal differentiation, considered "
                + "as a rational linear operator. The identity "
                + "(D-j)(p_j(X)E^j)=p_j'(X)E^j shows that p_j(X)E^j belongs "
                + "to the generalized eigenspace of D for eigenvalue j: "
                + "the power (D-j)^(degree(p_j)+1) annihilates it. "
                + "Generalized eigenspaces for distinct eigenvalues form an "
                + "independent family. Thus each summand of a zero sum vanishes. "
                + "The series E is a unit, so each p_j(X) vanishes, and injectivity "
                + "of the polynomial inclusion gives p_j=0. The proof uses "
                + "Mathlib's general independence theorem for generalized eigenspaces "
                + "and its differentiation and unit identities for the formal exponential.",
                DescribeRole.Theorem),
            Node("exp_transcendental", "Transcendence over the polynomial coefficient ring",
                "With the canonical inclusion Q[t] -> Q[[X]], t=X, the series E "
                + "is transcendental over Q[t]. This is the same injectivity statement "
                + "expressed through the algebra evaluation homomorphism Q[t][u] -> Q[[X]].",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("exponential-transcendence-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);
}
