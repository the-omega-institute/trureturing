using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TimeSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/TimeSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smallest prime zero rank bounds, and attains, the number of mutually recovering time observations.",
        H("Pairwise Fibonacci Time Recovery"),
        Blocks(
            Paragraph(Text("N includes zero. F is the Fibonacci sequence with F(0)=0 and F(1)=1. "
                + "The modulus n is a natural number, the state x=(a,b) lies in (Z/nZ)^2, and "
                + "time labels are natural numbers. Finset(N) denotes finite sets of distinct time labels; "
                + "range(k) is the set of labels from zero through k-1. All readout arithmetic is modulo n. "
                + "Natural infima are zero on the empty set. On positive moduli a positive Fibonacci "
                + "zero exists, since the invertible Fibonacci step permutes a finite state space.")),
            Node("readout", "Time readout", Disp(Equal(Call("r", Ids("n", "t", "x")),
                Seq(Call("F", F.Id("t")), Sp, F.Id("a"), Sp, Plus, Sp,
                    Call("F", Seq(F.Id("t"), Plus, D(1))), Sp, F.Id("b")))),
                "The step sends (a,b) to (b,a+b). Its second coordinate after t steps is r(n,t,x).",
                DescribeRole.Definition),
            Node("PairwiseRecovery", "Pairwise source recovery", PairwiseFormula(),
                "Recovery means injectivity on the whole state space, with the two time labels retained.",
                DescribeRole.Definition),
            Node("zeroRank", "Positive zero rank", Disp(Equal(Call("z", F.Id("p")),
                Call("inf", Seq(OpenBrace, F.Id("d"), Colon, F.Id("N"), Sp, Mid, Sp,
                    D(0), Lt, F.Id("d"), Sp, Land, Sp, F.Id("p"), Sp, Mid, Sp,
                    Call("F", F.Id("d")), CloseBrace)))),
                "For a prime p, z(p) is the least positive d such that p divides F(d).",
                DescribeRole.Definition),
            Node("recoveryLimit", "The least prime zero rank", Disp(Equal(Call("L", F.Id("n")),
                Call("inf", Seq(OpenBrace, Call("z", F.Id("p")), Sp, Mid, Sp,
                    Call("Prime", F.Id("p")), Sp, Land, Sp, F.Id("p"), Sp, Mid, Sp,
                    F.Id("n"), CloseBrace)))),
                "For n at least two, its prime divisors form a nonempty finite set, so this infimum is a minimum.",
                DescribeRole.Definition),
            Node("pairwise_recovery_maximum", "Sharp recovery capacity", ResultFormula(),
                "Two readings at s<t recover the source exactly when n and F(t-s) are coprime. "
                + "For a prime divisor p attaining L(n), time labels in a recovering set must have "
                + "distinct residues modulo z(p), which bounds the set size by L(n). Conversely, "
                + "positive differences between labels in range(L(n)) are smaller than every prime "
                + "zero rank. No prime divisor of n divides the corresponding Fibonacci number, "
                + "so every pair recovers. Since range(L(n)) has L(n) elements, the upper bound is attained.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("time-sampling-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula[] Ids(params string[] names) => names.Select(F.Id).ToArray();
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula PairwiseFormula() => Disp(Seq(
        Call("P", Ids("n", "T")), Sp, Leftrightarrow, Sp,
        Forall, Sp, F.Id("s"), Sp, InMacro, Sp, F.Id("T"), Comma, Sp,
        Forall, Sp, F.Id("t"), Sp, InMacro, Sp, F.Id("T"), Comma, Sp,
        Par(Seq(F.Id("s"), Lt, F.Id("t"))), Sp, Implies, Sp,
        Call("Injective", Seq(F.Id("x"), Sp, Mapsto, Sp,
            Par(Seq(Call("r", Ids("n", "s", "x")), Comma, Call("r", Ids("n", "t", "x"))))))));
    private static Formula ResultFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
        Par(Seq(D(2), Sp, Le, Sp, F.Id("n"))), Sp, Implies, Sp,
        Par(Seq(Call("P", F.Id("n"), Call("range", Call("L", F.Id("n")))), Sp, Land, Sp,
            Par(Seq(Forall, Sp, F.Id("T"), Sp, InMacro, Sp, Call("Finset", F.Id("N")), Comma, Sp,
                Call("P", Ids("n", "T")), Sp, Implies, Sp,
                Call("card", F.Id("T")), Sp, Le, Sp, Call("L", F.Id("n"))))))));
}
