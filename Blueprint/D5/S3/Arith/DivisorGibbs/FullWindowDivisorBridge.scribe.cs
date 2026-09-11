using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DivisorGibbs;

internal sealed class FullWindowDivisorBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/DivisorGibbs/FullWindowDivisorBridge.";
    private static Formula N => F.Id("n");
    private static Formula S => F.Id("s");
    private static Formula K => F.Id("k");
    private static Formula Dd => F.Id("d");
    private static Formula P => F.Id("p");
    private static Formula J => F.Id("j");
    private static Formula Window => Call("M", K);
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Product => Seq(Prod, Underscore,
        Grp(P, Sp, InMacro, Sp, Call("primeFactors", N)), Sp,
        Sum, Underscore, Grp(J, Eq, Num(0)), Caret, Grp(Call("factorization", N, P)), Sp,
        Pow(Pow(P, Seq(Minus, S)), J));
    private static Formula EulerClause => All("n", NatType, All("s", ComplexType,
        Implies(Seq(Num(0), Sp, Lt, Sp, N), Equal(Call("Z", N, S), Product))));
    private static Formula NonzeroClause => All("k", NatType, Seq(Window, Sp, Neq, Sp, Num(0)));
    private static Formula DivisibilityClause => All("d", NatType,
        Implies(Seq(Num(0), Sp, Lt, Sp, Dd),
            Seq(Exists, Sp, F.Id("K"), Sp, InMacro, Sp, NatType, Comma, Sp,
                All("k", NatType, Implies(Seq(F.Id("K"), Sp, Le, Sp, K),
                    Seq(Dd, Sp, Mid, Sp, Window))))));
    private static Formula TsumClause => All("k", NatType, All("s", ComplexType,
        Equal(Call("Z", Window, S), Seq(Sum, Underscore,
            Grp(Dd, Sp, InMacro, Sp, NatType), Sp,
            Call("indicator", Call("divisors", Window), Dd), Sp, Pow(Dd, Seq(Minus, S))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci prime-power windows are nonzero and exhaust every positive divisor.",
        H("Divisor polynomials along Fibonacci prime windows"),
        Blocks(
            Paragraph(Text("Write p(i) for Nat.nth Nat.Prime i, beginning with p(0)=2. "
                + "All indices are natural numbers and s is complex. The Fibonacci sequence "
                + "has fib(0)=0 and fib(1)=1. Write Z(n,s) for the sum of d to minus s "
                + "over the positive divisors of n, and factorization(n,p) for the "
                + "multiplicity of p. The indicator is one on its set and zero elsewhere. "
                + "The natural-indexed sum in the final clause denotes tsum.")),
            Describe.Lean(DescribeId.Create("full-window-product"),
                DeclarationHandle.Create(Module + "M"), H("The specified full window"),
                StatementSource.FromAuthor(Disp(Equal(Window, Seq(Prod, Underscore,
                    Grp(F.Id("i"), Sp, Lt, Sp, K), Sp,
                    Pow(Call("p", F.Id("i")), Subtract(Call("fib", Add(K, Num(2))), Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equivalently the product is over i in Finset.range k. "
                    + "For k=0 it is the empty product, equal to one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-divisor-bridge"),
                DeclarationHandle.Create(Module + "finite_divisor_bridge"),
                H("Euler factorization and cofinal finite sums"),
                StatementSource.FromAuthor(Disp(And(EulerClause,
                    And(And(NonzeroClause, DivisibilityClause), TsumClause)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Euler identity holds for every positive n and every "
                    + "complex s, including s=0. Each window is a product of nonzero prime powers. "
                    + "For each positive d, a single cutoff bounds both the indices of its "
                    + "prime factors and their multiplicities; every later Fibonacci window "
                    + "is divisible by d. The final clause extends each finite divisor sum "
                    + "by zero. These statements impose no convergence assumption on s and "
                    + "do not assert a limit outside an absolutely convergent half-plane."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Pow(Formula x, Formula y) => Seq(Grp(x), Caret, Grp(y));
}
