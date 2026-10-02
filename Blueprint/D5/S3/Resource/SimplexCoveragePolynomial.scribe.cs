using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SimplexCoveragePolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Resource/SimplexCoveragePolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual reciprocal-factorial represented spanning polynomials have exact contractions, a degree-two reverse bound, positive-evaluation support and zero obstructions.",
        H("Represented Spanning Polynomial Dependencies"),
        Blocks(
            Paragraph(Text(
                "Variables are indexed by physical columns over an arbitrary field. Zero, repeated and "
                + "scalar-parallel columns remain separate indices. Coefficients lie in Q and evaluation "
                + "lies in R; no characteristic-zero assumption on the column field is made.")),
            Definition("representedSpan", "Represented support span",
                "Adjoin to U the span of columns whose natural exponent is positive."),
            Definition("spanningPolynomial", "Actual reciprocal-factorial polynomial",
                "Sum the monomials of total degree m whose represented support spans the ambient space "
                + "together with U, weighting each by the product of reciprocal coordinate factorials. "
                + "The finite exponent encoding retains all physical indices."),
            Definition("evaluateAt", "Real evaluation",
                "Evaluate the rational polynomial at the represented real coordinate vector."),
            Definition("spanningHessian", "Actual algebraic Hessian",
                "Evaluate the two polynomial partial derivatives, not a separate support-indicator matrix."),
            Theorem("spanningPolynomial_coeff", "Exact represented coefficients",
                "At every natural exponent vector the coefficient is the reciprocal-factorial weight "
                + "exactly when its total equals the degree and its represented support spans with U; "
                + "otherwise the coefficient is zero. No finite-dimensional or nonempty assumption is needed."),
            Theorem("spanningPolynomial_pderiv", "Exact one-column contraction",
                "Differentiation at physical index i lowers successor degree by one and replaces U by "
                + "U plus the span of that column. Loops, repeats and scalar-parallel columns are included."),
            Theorem("spanningHessian_degree_two_classification", "Degree-two quotient-rank classification",
                "For finite-dimensional ambient space and arbitrary evaluation point, quotient rank zero "
                + "gives entries one; rank one excludes precisely loop-loop pairs; rank two joins nonloops "
                + "with distinct one-column extension subspaces; larger rank gives zero. Empty indices "
                + "and unspanned represented families are allowed."),
            Theorem("spanningPolynomial_degree_two_reverse", "Division-free degree-two reverse inequality",
                "In finite dimension, for nonnegative x and unrestricted real y, the actual polynomial F, "
                + "Hessian H and evaluated polynomial gradient g satisfy 2 F(x) y^T H y <= (g^T y)^2. "
                + "The zero-evaluation boundary and empty index set are included. Finite-fiber grouping "
                + "is a proof identity, not column deduplication or sampling renormalization."),
            Theorem("spanningPolynomial_positive_iff", "Positive evaluation and quotient rank",
                "For finite nonempty physical indices, finite-dimensional ambient space, strictly positive "
                + "x and U plus the full represented column span equal to the ambient space, F(x) is "
                + "nonnegative and strictly positive exactly when quotient rank is at most the degree. "
                + "Nonemptiness is needed for padding when U is already the whole space."),
            Theorem("spanningHessian_active_connected", "Actual derivative-positive support connectivity",
                "Under the same nonempty, finite-dimensional, positive-evaluation and full-spanning "
                + "conditions, at degree m+2 define active indices by the strictly positive evaluated "
                + "actual polynomial derivative. Every nonempty proper cut on this subtype has a "
                + "positive Hessian crossing. Empty and singleton active sets satisfy the cut condition "
                + "vacuously; this does not supply nonemptiness for the matrix normalization theorem."),
            Theorem("spanningPolynomial_eq_zero_of_rank_or_span", "Exact zero-polynomial obstructions",
                "In finite dimension the polynomial vanishes identically if its degree is less than "
                + "quotient rank or U plus the entire represented column span is not the whole space. "
                + "No nonempty, full-spanning or evaluation-point assumption is imposed."),
            Paragraph(Text(
                "These are reusable dependencies of the source-faithful development for "
                + "Bertuzzo–Ravagnani–Yaakobi, arXiv:2603.06489v1, Conjecture 3.2, preregistered in #11799. "
                + "No higher-degree reverse inequality, analytic derivative bridge, root concavity, "
                + "projective averaging, physical iid probability normalization, zero-column coupling "
                + "or actual expected-time optimizer is claimed. The full conjecture remains OPEN."))),
        []));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("simplex-coverage-polynomial-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
