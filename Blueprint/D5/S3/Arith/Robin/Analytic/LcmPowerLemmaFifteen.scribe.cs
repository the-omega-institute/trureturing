using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerLemmaFifteenDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real power inequality and its LCM power function comparison for every kappa>1.",
        H("The all-parameter LCM power comparison"),
        Blocks(
            Paragraph(Text(
                "The parameter kappa and the variable y are real. The powers with exponent "
                + "kappa are real powers; the square notation agrees with real exponent two.")),
            Describe.Lean(
                DescribeId.Create("lemma-fifteen-core"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_core"),
                H("The strict power inequality"),
                StatementSource.FromAuthor(CoreClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real kappa>1 and every real y>1 the displayed strict "
                        + "inequality holds. In particular, the parameter range includes 1<kappa<=3/2.")),
                    Paragraph(Text(
                        "Set s=1/y and h=1/y^2, so 0<h<s. With B(t)=log((1+t)^kappa-t^kappa), "
                        + "strict concavity gives B(s+h)-B(s)<B(2h)-B(h). Concavity up to zero "
                        + "and B(0)=0 give B(h)>=B(2h)/2. Thus "
                        + "2*(B(s+h)-B(s))<B(2h). The positive power differences allow "
                        + "exponentiation, and their common scaling by powers of y gives the claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lcm-power-function"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF"),
                H("The LCM power function"),
                StatementSource.FromAuthor(FunctionDefinition()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real kappa, x and a this is the total real-valued expression "
                    + "F(kappa,x,a). All occurrences of x^(a+1), x^a and the subsequent "
                    + "kappa powers are real powers. The comparison below uses its positive "
                    + "domain x>1, kappa>1 at a=1 and a=2. This is the function in "
                    + "Fan, Kobayashi and Molnar, A family of analogues to the Robin criterion, Definition 4.2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lemma-fifteen-function-comparison"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415_F"),
                H("Comparison at two and one"),
                StatementSource.FromAuthor(ComparisonClaim()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every real kappa>1 and every real y>sqrt(2), "
                        + "F(kappa,y,2)<F(kappa,y^2/2,1). Both bases are strictly greater than one. "
                        + "There is no assumption concerning the Riemann hypothesis.")),
                    Paragraph(Text(
                        "Write A=(y^2+2)^kappa-2^kappa, "
                        + "B=(y^2+y+1)^kappa-(y+1)^kappa and C=(y+1)^kappa-1. "
                        + "Factoring the cubic and quadratic expressions gives "
                        + "F(kappa,y,2)=log(B/(C*y^kappa))/(kappa*log(y)) and "
                        + "F(kappa,y^2/2,1)=log(A/y^(2*kappa))/(kappa*log(y^2/2)). "
                        + "Strict superadditivity of positive real powers gives A>y^(2*kappa), "
                        + "so the latter numerator is positive. The core inequality gives "
                        + "2*log(B/(C*y^kappa))<log(A/y^(2*kappa)). "
                        + "Finally 0<log(y^2/2)<2*log(y), with kappa>0, gives the strict comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lemma-fifteen"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415"),
                H("Lemma 4.15 for every kappa greater than one"),
                StatementSource.FromAuthor(FullClaim()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For all real kappa>1 and x,xprime>1, the equation "
                        + "F(kappa,xprime,2)=F(kappa,x,1) implies xprime<sqrt(2*x). "
                        + "In the source notation x=x_1 and xprime=x_2: both are characterized "
                        + "by F(kappa,x_1,1)=epsilon=F(kappa,x_2,2). Thus this implication "
                        + "gives the assertion of Lemma 4.15 for every kappa>1 and epsilon>0. "
                        + "It holds for every solution of the equation, without using the "
                        + "source Theorem 4.3 or any existence or inverse-function theorem.")),
                    Paragraph(Text(
                        "Set r=t/(1+t). The elasticity t*B'(t) equals "
                        + "kappa*(1-1/((1-r^kappa)/(1-r))). Strict convexity of r^kappa "
                        + "makes its secant slope to 1 strictly increasing, so the elasticity "
                        + "is strictly increasing on t>0. The derivative of "
                        + "g(s)=B(s+s^2)-B(s) is positive, and g itself is positive. "
                        + "Since F(kappa,x,2)=g(1/x)/(kappa*log(x)), this function is "
                        + "strictly decreasing on x>1. Apply the comparison at y=sqrt(2*x) "
                        + "and then this strict decrease to obtain xprime<y."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fan-kobayashi-molnar-2026-remark-4-16"),
                    ResolutionKind.Proved)))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Quotient(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesClaim(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula CoreClaim()
    {
        var k = F.Id("kappa");
        var y = F.Id("y");
        var a = Subtract(Pow(Add(Pow(y, D(2)), D(2)), k), Pow(D(2), k));
        var b = Subtract(Pow(Add(Add(Pow(y, D(2)), y), D(1)), k), Pow(Add(y, D(1)), k));
        var c = Subtract(Pow(Add(y, D(1)), k), D(1));
        return Disp(All("kappa", Real, All("y", Real,
            ImpliesClaim(And(Less(D(1), k), Less(D(1), y)),
                Less(Pow(b, D(2)), Multiply(a, Pow(c, D(2))))))));
    }

    private static Formula FunctionDefinition()
    {
        var k = F.Id("kappa");
        var x = F.Id("x");
        var a = F.Id("a");
        var successorPower = Pow(x, Add(a, D(1)));
        var currentPower = Pow(x, a);
        var numerator = Subtract(Pow(Subtract(successorPower, D(1)), k),
            Pow(Subtract(currentPower, D(1)), k));
        var denominator = Subtract(Pow(Subtract(successorPower, x), k),
            Pow(Subtract(currentPower, x), k));
        return Disp(All("kappa", Real, All("x", Real, All("a", Real,
            Equal(Call("lcmPowerF", k, x, a),
                Quotient(Call("log", Quotient(numerator, denominator)),
                    Multiply(k, Call("log", x))))))));
    }

    private static Formula FullClaim()
    {
        var k = F.Id("kappa");
        var x = F.Id("x");
        var xp = F.Id("xprime");
        return Disp(All("kappa", Real, All("x", Real, All("xprime", Real,
            ImpliesClaim(And(And(Less(D(1), k), Less(D(1), x)),
                And(Less(D(1), xp), Equal(Call("lcmPowerF", k, xp, D(2)),
                    Call("lcmPowerF", k, x, D(1))))),
                Less(xp, Call("sqrt", Multiply(D(2), x))))))));
    }

    private static Formula ComparisonClaim()
    {
        var k = F.Id("kappa");
        var y = F.Id("y");
        return Disp(All("kappa", Real, All("y", Real,
            ImpliesClaim(And(Less(D(1), k), Less(Call("sqrt", D(2)), y)),
                Less(Call("lcmPowerF", k, y, D(2)),
                    Call("lcmPowerF", k, Quotient(Pow(y, D(2)), D(2)), D(1)))))));
    }
}
