using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexInitialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinConvexInitial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The analytic bias quotient has exact initial derivatives through order four.",
        H("Initial Jets of the Riccati Quotient"),
        Blocks(
            Paragraph(Text("For n different from zero, desingularize the odd power difference by its divided difference at zero. "
                + "Mathlib's binomial power series and its analytic divided-difference theorem provide a smooth quotient near zero. "
                + "The initial data are computed from that exact series, using the Leibniz rule on the quotient identity.")),
            Node("H", "Divided power difference", "H_n(t) = dslope(s ↦ (1+s)^n − (1−s)^n, 0, t)",
                DescribeRole.Definition, "At zero, dslope uses the derivative, so H_n(0)=2n."),
            Node("K", "Even power sum", "K_n(t) = (1+t)^n + (1−t)^n", DescribeRole.Definition,
                "This even real-power expression has value two at zero."),
            Node("Q", "Desingularized bias quotient", "Q_n(t) = n K_n(t)/H_n(t)", DescribeRole.Definition,
                "The quotient is total as a real function, and analytic near zero when n is nonzero."),
            Node("H_zero", "Initial denominator", "H_n(0) = 2n", DescribeRole.Theorem,
                "The first coefficient of the odd power difference is 2n."),
            Node("Q_analyticAt_zero", "Analytic extension", "n ≠ 0 → AnalyticAt R Q_n 0", DescribeRole.Theorem,
                "The denominator at zero is 2n, hence is nonzero under the stated hypothesis."),
            Node("Q_zero", "Initial quotient", "n ≠ 0 → Q_n(0) = 1", DescribeRole.Theorem,
                "The quotient of n times the initial numerator two and the denominator 2n is one."),
            Node("Q_eq", "Agreement with the punctured formula",
                "t ≠ 0 → Q_n(t) = nt ((1+t)^n+(1−t)^n)/((1+t)^n−(1−t)^n)", DescribeRole.Theorem,
                "Away from zero, the divided difference is the power difference divided by t."),
            Node("Q_jets", "Exact initial derivatives",
                "n ≠ 0 → Q_n'(0)=0 ∧ Q_n''(0)=2(n^2−1)/3 ∧ Q_n'''(0)=0 ∧ Q_n''''(0)=−8(1−n^2)(4−n^2)/15",
                DescribeRole.Theorem,
                "The binomial coefficients give the denominator and numerator derivatives. "
                + "Differentiating Q_n H_n=n K_n through order four determines these four derivatives. "
                + "For 0 < n <= 1/4 the second and fourth derivatives are strictly negative."),
            Node("Q_local_derivatives", "Local derivative chain",
                "n ≠ 0 → ∃a>0, (∀t∈[0,a], ∀k, HasDerivAt (D^k Q_n) (D^(k+1) Q_n(t)) t) ∧ ContinuousAt (D^4 Q_n) 0",
                DescribeRole.Theorem,
                "Analyticity holds throughout a neighborhood of zero, so all iterated derivatives exist there. "
                + "These certificates are consumed by the square-root reparametrization and its local sign argument."))));

    private static DocumentBlock Node(string name, string title, string formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("cachin-convex-initial-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(formula)), Paragraph(Text(prose))), role);
}
