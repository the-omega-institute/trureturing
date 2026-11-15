using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class BalaA119370ExponentialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/bala2024a119370");
    private static readonly LibraryNoteRef Gessel = LibraryNoteRef.Create("D5/L/PermutationPatterns/gessel2016lagrange");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independently normalized A119370 quadratic series equals Bala's formal exponential at every coefficient, and agrees with the printed constant-one square-root branch.",
        H("Bala's A119370 exponential identity"),
        Blocks(
            Paragraph(Text("All series have rational coefficients. The topology used to express HasSum is coefficientwise convergence with discrete rational coefficients; each coefficient below is a finite sum. No analytic convergence assumption is made.")),
            Node("IsSourceSeries", "The independent quadratic source",
                All("A", PS(), IffOf(Call("IsSourceSeries", V("A")), SourceBody(V("A")))),
                "OEIS A119370, revision 37, NAME: \"G.f. satisfies A(x) = 1 + x*A(x)^2 + x^2*(A(x)^2 - A(x)).\" The constant coefficient is one. The source is specified by this equation before any exponential is used.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("row", "The full finite binomial-square row",
                All("n", N(), EqOf(Call("row", V("n")), RowBody())),
                "The finite sum in Bala's FORMULA runs from k=0 through k=n. Its scalar binomial square is embedded as a constant series. The X in each factor is the same formal variable as the outer power of X in the logarithm.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("logarithm", "The locally finite logarithmic sum",
                All("m", N(), EqOf(Coeff(V("m"), V("logarithm")), LogCoefficient())),
                "This defines the whole series L by its degree-m coefficient. Only positive indices n through m occur. Equivalently L is the sum of X^n row(n)/n for n at least one. Its constant coefficient is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("formalExp", "The formal exponential",
                All("f", PS(), EqOf(Call("formalExp", V("f")), Qualified("PowerSeries", "subst", V("f"), Qualified("PowerSeries", "exp", Q())))),
                "At a zero-constant inner series f, this is the admissible substitution of f into the formal exponential. Its coefficients are the sums of f^j/j!, including j=0. The result below proves both the whole formal sum and the explicit degree-m finite formula for L.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("discriminant", "The printed discriminant",
                EqOf(V("discriminant"), Sub(Pow(Add(D(1), Pow(V("X"), D(2))), D(2)), Mul(Mul(D(4), V("X")), Add(D(1), V("X"))))),
                "OEIS A119370, FORMULA: \"A(x) = ((1+x^2) - sqrt( (1+x^2)^2 - 4*x*(1+x) ))/(2*x*(1+x)).\" The selected square root has constant coefficient one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("printedBranch", "Lawful division in the printed branch",
                PrintedBranchFormula(),
                "After proving the numerator divisible by X, its coefficient shift removes that factor. The remaining denominator 2(1+X) has constant coefficient two and is a unit. This expression never inverts X.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("result", "The complete exponential identity and branch correspondence", FullResult(),
                "A normalized coefficient contraction constructs the unique source A independently. A second contraction constructs C in Q[Y][[z]] with C(0)=1 and C=(1+zC)(1+YzC). For each rational y, put f=zC_y and R(t)=(1+t)(1+yt). Apply the original rational power-coefficient Lagrange theorem inside the logarithmic client. The derivative of log R times R is R'; the finite coefficient sum gives n[z^n]log C_y=[t^n]R(t)^n. Binomial convolution gives the complete square-binomial row. Polynomial extensionality lifts this identity from every rational y to Q[Y]. The existing continuous diagonal evaluates z=X and Y=1+X, retaining only outer indices n<=m in degree m. It preserves the logarithmic substitution and identifies log b=L for b=D(C). Its quadratic implies that 1+Xb satisfies the original source equation. Original-source uniqueness and formal exp/log inversion give A=1+X Exp(L). Finally S=1+X^2-2X(1+X)A has the required square. Any other normalized root T satisfies (T-S)(T+S)=0; T+S is a unit with constant coefficient two, so T=S. The numerator equals X*2(1+X)A, which proves the stated shift and unit quotient. The coefficient-zero identity, all finite-row endpoints and the exponential's zeroth power are included.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Gessel),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala-a119370-exponential"), ResolutionKind.Proved))),
        edges: [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/Congruence/TebniA350759PrimeCongruences"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("balaa119370-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, Formula body) => Seq(Exists, Bang, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) => Par(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula EqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(params Formula[] fs) => fs.Length == 1 ? fs[0] :
        new Formula.Logic(Par(fs[0]), FormulaLogicOperator.And, Par(And(fs[1..])));
    private static Formula CastQ(Formula f) => Par(Seq(f, Colon, Sp, Q()));
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Constant(Formula f) => Call("constantCoeff", f);
    private static Formula SumOver(string n, Formula set, Formula body) => Qualified("Finset", "sum", set, Lam(n, N(), body));
    private static Formula InvNat(Formula n) => new Formula.Fraction(D(1), CastQ(n));
    private static Formula SourceBody(Formula a) => And(EqOf(Constant(a), D(1)),
        EqOf(a, Add(Add(D(1), Mul(V("X"), Pow(a, D(2)))), Mul(Pow(V("X"), D(2)), Sub(Pow(a, D(2)), a)))));
    private static Formula RowBody() => SumOver("k", Call("range", Add(V("n"), D(1))),
        Mul(Call("C", Pow(CastQ(Qualified("Nat", "choose", V("n"), V("k"))), D(2))), Pow(Add(D(1), V("X")), V("k"))));
    private static Formula LogCoefficient() => SumOver("n", Call("Icc", D(1), V("m")),
        Mul(InvNat(V("n")), Coeff(Sub(V("m"), V("n")), Call("row", V("n")))));
    private static Formula LogTerm(Formula n) => Mul(Mul(Call("C", InvNat(n)), Call("row", n)), Pow(V("X"), n));
    private static Formula ExpTerm(Formula j) => Mul(Call("C", InvNat(Qualified("Nat", "factorial", j))), Pow(V("logarithm"), j));
    private static Formula Numerator(Formula s) => Sub(Add(D(1), Pow(V("X"), D(2))), s);
    private static Formula Root(Formula s) => And(EqOf(Constant(s), D(1)), EqOf(Pow(s, D(2)), V("discriminant")));
    private static Formula ExponentialAnswer() => Add(D(1), Mul(V("X"), Call("formalExp", V("logarithm"))));
    private static Formula PrintedBranchFormula()
    {
        var shift = Qualified("PowerSeries", "mk", Lam("n", N(),
            Coeff(Add(V("n"), D(1)), Numerator(V("S")))));
        var unitInverse = Pow(Mul(D(2), Add(D(1), V("X"))), Seq(Minus, D(1)));
        return All("S", PS(), EqOf(Call("printedBranch", V("S")), Mul(shift, unitInverse)));
    }

    private static Formula FullResult()
    {
        var finiteLog = All("m", N(), All("n", N(), Imp(Seq(V("m"), Lt, V("n")),
            EqOf(Coeff(V("m"), LogTerm(V("n"))), D(0)))));
        var finiteExp = All("m", N(), All("j", N(), Imp(Seq(V("m"), Lt, V("j")),
            EqOf(Coeff(V("m"), Pow(V("logarithm"), V("j"))), D(0)))));
        var expCoefficient = All("m", N(), EqOf(Coeff(V("m"), Call("formalExp", V("logarithm"))),
            SumOver("j", Call("range", Add(V("m"), D(1))),
                Mul(InvNat(Qualified("Nat", "factorial", V("j"))),
                    Coeff(V("m"), Pow(V("logarithm"), V("j")))))));
        var branch = All("S", PS(), Imp(EqOf(Constant(V("S")), D(1)),
            Imp(EqOf(Pow(V("S"), D(2)), V("discriminant")), And(
                Seq(V("X"), Mid, Numerator(V("S"))), EqOf(V("A"), Call("printedBranch", V("S")))))));
        var sourceAnswer = All("A", PS(), Imp(Call("IsSourceSeries", V("A")), And(
            EqOf(V("A"), ExponentialAnswer()),
            All("m", N(), EqOf(Coeff(V("m"), V("A")), Coeff(V("m"), ExponentialAnswer()))),
            Unique("S", PS(), Root(V("S"))), branch)));
        return And(
            Unique("A", PS(), Call("IsSourceSeries", V("A"))),
            EqOf(Constant(V("logarithm")), D(0)),
            Call("HasSum", Lam("n", N(), LogTerm(Add(V("n"), D(1)))), V("logarithm")),
            finiteLog,
            Call("HasSum", Lam("j", N(), ExpTerm(V("j"))), Call("formalExp", V("logarithm"))),
            finiteExp, expCoefficient, sourceAnswer);
    }
}
