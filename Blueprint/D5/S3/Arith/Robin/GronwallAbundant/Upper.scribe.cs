using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.GronwallAbundant;

internal sealed class UpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-deletion constraints, missing-prime mass and finite-code entropy for proper GA1 integers.",
        H("Upper"),
        Blocks(
            Paragraph(Text("For a proper GA1 integer put T=log(N). Deleting any prime leaves at least four. The exact normalized divisor-sum ratio gives S*(log(log(N))-log(log(N/p)))<=log(log(N)), where S=1+p+...+p^v. The logarithmic gap is at least log(p)/T. CNS Theorem 9 gives p^r<=r*T for every occupied positive layer r; in particular every prime factor is at most T and every repeated prime is at most sqrt(2*T).")),
            Paragraph(Text("If P is the largest prime factor, W is the logarithmic mass of missing primes below P, and E is the mass beyond first prime copies, then T=theta(P)-W+E. Thus W<=psi(P)-P+E. For log(N)<=X, E<=72*X^(3/4). Splitting P at sqrt(X) makes the quantitative prime number theorem uniform over every smaller prefix. The fixed-power repetition term is absorbed into the same exponential power-logarithm allowance.")),
            Paragraph(Text("The integer is recovered from P, all exponents below floor(sqrt(2*X))+1, and the omitted large primes. A coarse exponent range through ceil(2*X) suffices. Each omitted large prime has logarithmic mass at least log(X)/2, so at most ceil(2*B/log(X))+1 are omitted when W<=B. Unique prime factorization makes this code injective. Weighted binomial sums bound its missing-set cost by K*(1+log(M/K)).")),
            Paragraph(Text("The rounded finite coordinates cost O(sqrt(X)*log(X)); the entropy and this cost are bounded by D*(X/log(X))*exp(-a*(log(X))^(1/10)) with positive a. If c0 is the MediumPNT constant, the uniform budget uses c=c0*2^(-1/10) and the terminal estimate uses a=c/2=c0*2^(-1/10)/2. Substituting X=log(x) gives the displayed bound for the original counting function. The constants and starting point are existential. No lower count estimate or conditional sharper upper scale is asserted.")),
            Paragraph(Text("This is one strict improvement answering the request in section 8 of Caveney, Nicolas and Sondow. The proved mechanism combines the same-integer prime endpoint barrier with missing-prime mass controlled by psi(y)-y. A lower counting bound depends on sign oscillations of theta(y)-y; that bridge remains unresolved. Under RH, a candidate scale for log(1+Q1(x)) is sqrt(log(x))*(log(log(x)))^O(1); no such conditional improvement is proved here.")),
            Describe.Lean(DescribeId.Create("ga1-log-count-le-cost"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Upper.ga1_log_count_le_cost"), H("The actual counting function is bounded by the logarithmic cost of its injective code."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual counting function is bounded by the logarithmic cost of its injective code."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Upper.result"), H("The proper GA1 counting function has an exponential power-logarithm saving."),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proper GA1 counting function has an exponential power-logarithm saving."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var a = F.Id("a"); var c = F.Id("C"); var r = F.Id("r"); var x = F.Id("x");
        var lx = Call("log", x); var llx = Call("log", lx);
        var saving = Call("exp", Negate(Mul(a, new Formula.Power(llx, Div(D(1), D(1,0))))));
        var bound = Le(Call("log", Add(D(1), new Formula.Apply(new Formula.Subscript(F.Id("Q"), D(1)), [x]))), Mul(Mul(c, Div(lx, llx)), saving));
        var tail = All("x", Implies(Le(r, x), bound));
        return Disp(Ex("a", And(Lt(D(0), a), Ex("C", And(Lt(D(0), c), Ex("r", tail))))));
    }
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string n, Formula b) => Seq(Forall, Sp, F.Id(n), Colon, Sp, Reals(), Comma, Sp, b);
    private static Formula Ex(string n, Formula b) => Seq(Exists, Sp, F.Id(n), Colon, Sp, Reals(), Comma, Sp, b);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [.. a]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Negate(Formula a) => Seq(Minus, a);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
