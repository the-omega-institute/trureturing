using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ExponentialPoleObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/ExponentialPoleObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational function u/(2-u) has no primitive when the derivative of u is u.",
        H("A Simple Pole Obstructs a Rational Primitive"),
        Blocks(
            Paragraph(Text(
                "Let K be a field of characteristic zero and let d be an integer-linear "
                + "derivation of K[u] satisfying d(u)=u. The restriction of d to K may "
                + "be nonzero. The conclusions therefore apply to the differential "
                + "field K=Q(t), with d(t)=1, as well as to constant coefficient fields.")),
            Describe.Lean(
                DescribeId.Create("exponential-polynomial-pole-obstruction"),
                DeclarationHandle.Create(Prefix + "polynomial_obstruction"),
                H("The Cleared Polynomial Identity Is Impossible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For coprime polynomials p,q with q nonzero, the identity "
                    + "(2-u)(d(p)q-pd(q))=u q² is impossible. Evaluating at u=2 "
                    + "first shows q(2)=0. Coprimality gives p(2) nonzero. Write "
                    + "q=(u-2)^(n+1)s with s(2) nonzero. Since d(u-2)=u, "
                    + "cancelling (u-2)^(n+1) in the proposed identity and evaluating "
                    + "again gives 2(n+1)p(2)s(2)=0. Every factor is nonzero. "
                    + "The factorization uses polynomial root multiplicity; no "
                    + "analytic convergence or complex residues are required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exponential-differential-evaluation-obstruction"),
                DeclarationHandle.Create(Prefix + "rational_expression_obstruction"),
                H("Injective Differential Evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let j inject K[u] into a field L with derivation D, and suppose "
                    + "D(j(p))=j(d(p)) for every polynomial p. For every reduced "
                    + "fraction p/q, its image j(p)/j(q) cannot have derivative "
                    + "j(u)/(2-j(u)). The quotient rule and clearing the two "
                    + "nonzero denominators would give the impossible polynomial "
                    + "identity above; injectivity of j returns that identity "
                    + "from L to K[u]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exponential-no-rational-primitive"),
                DeclarationHandle.Create(Prefix + "no_rational_primitive"),
                H("No Primitive in K(u)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If D is a derivation on K(u) that agrees with d on K[u], "
                    + "then D(h) differs from u/(2-u) for every rational function h. "
                    + "The reduced numerator and denominator of h supply coprime "
                    + "polynomials, so the differential evaluation obstruction "
                    + "applies to the standard embedding K[u] into K(u)."))),
                DescribeRole.Theorem))));
}
