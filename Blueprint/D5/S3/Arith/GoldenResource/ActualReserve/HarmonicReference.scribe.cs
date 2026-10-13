using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource.ActualReserve;

internal sealed class HarmonicReferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inclusive harmonic prime-power reference has a finite maximum at every real scale x > 1.",
        H("Finite Harmonic Reference"),
        Blocks(
            Paragraph(Text("Set lambda_x = 1/(x log x), v_p(x) = Nat.log p floor(x), "
                + "Q_p(a) = sum from k = 1 to a of 1/(k p^k), and H_p(a) = Q_p(a) - lambda_x a log p. "
                + "The primes in T_x are precisely the actual primes p <= x. "
                + "P(x) sums Q_p(v_p), psi(x) sums v_p log p, and F(x) = P(x) - lambda_x psi(x). "
                + "The cutoff theorem makes these the inclusive prime-power sums of original theory section 87.")),
            Describe.Lean(DescribeId.Create("harmonic-reference-inclusive-cutoff"),
                DeclarationHandle.Create(Prefix + "reference_cutoff_spec"),
                H("Inclusive cutoff"), StatementSource.FromAuthor(CutoffFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every natural exponent k, prime p and real x > 1, k <= v_p(x) "
                    + "if and only if p^k <= x. The Nat.log Galois connection and floor equivalence "
                    + "give finiteness and preserve a prime power equal to the real endpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("harmonic-reference-exact-gain-sign"),
                DeclarationHandle.Create(Prefix + "reference_gain_nonneg_iff"),
                H("Exact gain sign"), StatementSource.FromAuthor(SignFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For k >= 1 the reference gain is nonnegative exactly when p^k <= x. "
                    + "Positive denominators transform this into p^k log(p^k) <= x log x. "
                    + "Mathlib's strict monotonicity of t log t supplies the equivalence. "
                    + "At p^k = x the gain is zero, so either equality-layer choice preserves the value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("harmonic-reference-unbounded-exponent-maximum"),
                DeclarationHandle.Create(Prefix + "reference_objective_maximal"),
                H("Maximum against all exponents"), StatementSource.FromAuthor(MaximumFormula(false)),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every natural a, including zero and a beyond the finite carrier, H_p(a) <= H_p(v_p). "
                    + "The objective increases through nonnegative gains and decreases after the cutoff. "
                    + "This is reference optimization; the existing actual marginal optimizer has a different objective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-prefix-to-harmonic-reference-maximum"),
                DeclarationHandle.Create(Prefix + "actual_local_le_reference_maximum"),
                H("Actual prefix dominated by the reference maximum"),
                StatementSource.FromAuthor(MaximumFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix "
                    + "compares the whole geometric prefix to the harmonic prefix. Exponent zero has both values zero. "
                    + "Subtracting the same cost and using the preceding maximum yields u_p(a) <= H_p(v_p). "
                    + "No comparison of individual actual and reference marginals is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("harmonic-reference-finite-ambient-prime-sum"),
                DeclarationHandle.Create(Prefix + "reference_pressure_sum_on"),
                H("Exact sum on any finite actual-prime superset"),
                StatementSource.FromAuthor(SumFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite set U of actual primes containing T_x, F(x) is "
                    + "the sum of H_p(v_p) over U. A prime outside T_x has v_p = 0 and contributes zero. "
                    + "ActualReservePrimeMask uses U = T_x union n.primeFactors, so primes of the actual integer "
                    + "beyond the reference cutoff are retained in the complement."))), DescribeRole.Theorem))));

    private static Formula CutoffFormula() => Disp(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("p"), Comma,
        F.Id("k"), Comma, Sp, F.Id("x"), Gt, D(1), Land, Call("Prime", F.Id("p")), Rightarrow,
        Grp(Seq(F.Id("k"), Le, Call("v", F.Id("x"), F.Id("p")), Iff,
            new Formula.Power(F.Id("p"), F.Id("k")), Le, F.Id("x")))));

    private static Formula SignFormula() => Disp(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("p"), Comma,
        F.Id("k"), Comma, Sp, F.Id("x"), Gt, D(1), Land, Call("Prime", F.Id("p")), Land,
        F.Id("k"), Ge, D(1), Rightarrow, Grp(Seq(D(0), Le,
            new Formula.Fraction(D(1), Seq(F.Id("k"), new Formula.Power(F.Id("p"), F.Id("k")))),
            Minus, Seq(F.Id("lambda"), Call("log", F.Id("p"))), Iff,
            new Formula.Power(F.Id("p"), F.Id("k")), Le, F.Id("x")))));

    private static Formula MaximumFormula(bool actual) => Disp(Seq(Forall, Sp,
        F.Id("x"), Comma, F.Id("p"), Comma, F.Id("a"), Comma, Sp,
        F.Id("x"), Gt, D(1), Land, Call("Prime", F.Id("p")), Rightarrow,
        Call(actual ? "u" : "H", F.Id("x"), F.Id("p"), F.Id("a")), Le,
        Call("H", F.Id("x"), F.Id("p"), Call("v", F.Id("x"), F.Id("p")))));

    private static Formula SumFormula() => Disp(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("U"), Comma, Sp,
        F.Id("x"), Gt, D(1), Land, Call("ActualPrimeSuperset", F.Id("U"), Call("T", F.Id("x"))),
        Rightarrow, Call("F", F.Id("x")), Eq, Sum, Underscore, Grp(Seq(F.Id("p"), InMacro, F.Id("U"))),
        Sp, Call("H", F.Id("x"), F.Id("p"), Call("v", F.Id("x"), F.Id("p")))));

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
}
