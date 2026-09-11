using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DivisorGibbs;

internal sealed class FiniteDivisorEulerProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.";
    private static Formula N => F.Id("n");
    private static Formula S => F.Id("s");
    private static Formula Dd => F.Id("d");
    private static Formula P => F.Id("p");
    private static Formula J => F.Id("j");
    private static Formula Term => Pow(Dd, Seq(Minus, S));
    private static Formula DivisorSum => Seq(Sum, Underscore,
        Grp(Dd, Sp, InMacro, Sp, Call("divisors", N)), Sp, Term);
    private static Formula Product => Seq(Prod, Underscore,
        Grp(P, Sp, InMacro, Sp, Call("primeFactors", N)), Sp,
        Sum, Underscore, Grp(J, Eq, Num(0)), Caret, Grp(Call("factorization", N, P)), Sp,
        Pow(Pow(P, Seq(Minus, S)), J));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex divisor sums factor into finite geometric products for every exponent.",
        H("Finite Euler products for divisor sums"),
        Blocks(
            Paragraph(Text("The variables n, d, p and j are natural numbers, and s is complex. "
                + "The set divisors(n) contains the positive divisors and is empty for n=0. "
                + "The set primeFactors(n) contains distinct prime divisors; factorization(n,p) "
                + "is the multiplicity of p. Complex powers use the principal logarithm.")),
            Entry("Z", "The divisor Dirichlet polynomial",
                Eqn(Call("Z", N, S), DivisorSum),
                "Sum over the actual divisors of n. This definition also assigns zero at n=0.",
                DescribeRole.Definition),
            Entry("divisor_sum_eq_euler_product", "Finite Euler factorization",
                Disp(Seq(Forall, Sp, N, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    S, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Num(0), Sp, Lt, Sp, N, Sp, Rightarrow, Sp,
                    Call("Z", N, S), Sp, Eq, Sp, Product)),
                "Convolving the multiplicative complex power function with the arithmetic zeta "
                    + "function gives the divisor sum. Multiplicative factorization reduces it "
                    + "to prime powers, whose divisors are the powers from zero through the "
                    + "prime multiplicity. The power function is assigned zero at the natural "
                    + "index zero for this convolution; that index is never a positive divisor. "
                    + "No restriction on s is needed: at s=0 every local summand equals one."),
            Entry("divisor_sum_eq_tsum", "Zero outside the divisor set",
                Disp(Seq(Forall, Sp, N, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    S, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Call("Z", N, S), Sp, Eq, Sp,
                    Sum, Underscore, Grp(Dd, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N"))), Sp,
                    Call("indicator", Call("divisors", N), Dd), Sp, Term)),
                "Here indicator(A,d) is one on A and zero off A. The displayed natural-indexed "
                    + "sum is the infinite sum tsum. Its summands vanish outside the finite "
                    + "divisor set, so it equals the finite sum without any convergence "
                    + "condition on s. This includes n=0 and s=0."))));

    private static DocumentBlock Entry(string declaration, string title, Formula statement,
        string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("divisor-euler-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Factorization/mathlib2026divisoreuler")),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Pow(Formula x, Formula y) => Seq(Grp(x), Caret, Grp(y));
    private static Formula Eqn(Formula x, Formula y) => Disp(Equal(x, y));
}
