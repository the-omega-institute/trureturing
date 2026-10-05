using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class UnitShiftNormBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget.";
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula x, Formula p) => new Formula.Power(x, p);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual coordinate normalization imposes a cubic shift cost and joint growth budgets.",
        H("Unit Shift Norm Budget"),
        Blocks(
            Paragraph(Text("Write phi=(1+sqrt(5))/2, psi=1-phi, q(a,b)=2a+3b, "
                + "and Q(a,b)=a^2+ab-b^2. For natural j and g, put A=F(j-1), B=F(j), "
                + "where F is the Fibonacci sequence. The source quantity is N=gq(A,B)+1. "
                + "The integer r shifts the composition after absorbing its unit bit. "
                + "The two real embeddings and the golden norm are those of the golden integer ring.")),
            Describe.Lean(DescribeId.Create("unit-shift-composition"),
                DeclarationHandle.Create(Prefix + "shiftedComposition"), H("The actual shift"),
                StatementSource.FromAuthor(Disp(Seq(Call("y", V("j"), V("g"), V("r")), Eq,
                    Open, V("gA"), Plus, D(3), V("r"), Minus, D(1), Comma,
                    V("gB"), Plus, D(1), Minus, D(2), V("r"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shifted golden integer has coordinates "
                    + "gA+3r-1 and gB+1-2r. Its quantity is N for every integer shift."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unit-shift-source-quantity"),
                DeclarationHandle.Create(Prefix + "sourceQuantity"), H("Source quantity"),
                StatementSource.FromAuthor(Disp(Seq(V("N"), Eq, V("g"),
                    Open, D(2), V("A"), Plus, D(3), V("B"), Close, Plus, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unit bit contributes one to the multiplied "
                    + "Fibonacci composition quantity. For positive j, q(A,B)=F(j+3)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unit-shift-primitive-quantity"),
                DeclarationHandle.Create(Prefix + "primitiveQuantity"), H("Primitive quantity"),
                StatementSource.FromAuthor(Disp(Seq(V("U"), Eq, Fr(V("N"), V("d"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here d is the gcd of the absolute values of the "
                    + "two actual shifted coordinates. The normalized quantity U=N/d is "
                    + "defined by real division; the theorem ensures d is positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unit-shift-primitive-norm"),
                DeclarationHandle.Create(Prefix + "primitiveNorm"), H("Primitive norm"),
                StatementSource.FromAuthor(Disp(Seq(V("D"), Eq,
                    Fr(Seq(Lvert, Call("Q", V("y")), Rvert), P(V("d"), D(2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized absolute norm divides the existing "
                    + "golden norm by d squared. It uses the same actual coordinate gcd as U."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unit-shift-cubic-joint-budget"),
                DeclarationHandle.Create(Prefix + "result"), H("Cubic cost and joint budgets"),
                StatementSource.FromAuthor(Contract()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every j>=3, g>=2, and integer r, assume "
                        + "-1<g(A+Bpsi)<phi-1 and both shifted coordinates are nonnegative. "
                        + "Then the first strict inequality in the display holds with R=1+abs(r). "
                        + "For every pair of nonnegative real exponents alpha and beta with "
                        + "4alpha+3beta<1, the additional conditions g<=N^alpha and abs(r)<=N^beta "
                        + "give the two power inequalities uniformly over these sources and shifts. "
                        + "Moreover U tends uniformly to infinity: for each real M there is a threshold "
                        + "depending only on alpha, beta, and M above which every such U is at least M.")),
                    Paragraph(Text("The coordinate gcd divides "
                        + "P=r^2-3r+1+g^2(-1)^j. For g>=2 this polynomial never vanishes at an "
                        + "integer r: its even case is positive after completing a square; in its "
                        + "odd case a hypothetical zero would put an integer square strictly "
                        + "between (2g)^2 and (2g+1)^2. Consequently d<=(g^2+1)R^2.")),
                    Paragraph(Text("The conjugate embedding of the actual shifted integer is "
                        + "w-phi+r(2phi+1), where w=g(A+Bpsi). The source interval gives its "
                        + "absolute value strictly greater than R/2. Nonnegative coordinates "
                        + "and phi>3/2 give the other embedding at least N/2. Their product "
                        + "therefore has absolute norm strictly greater than NR/4. Combining "
                        + "these bounds for the same shift proves the cubic cost. The estimates "
                        + "g^2+1<=5g^2/4 and R<=2N^beta yield the constants 50 and 5.")),
                    Paragraph(Text("For each fixed 0<omega<1/2 there is a threshold T depending "
                        + "only on alpha, beta, and omega. Whenever N>=T and the same hypotheses "
                        + "hold, log(log(2+D)) is strictly larger than log(log(log(U)))^omega. "
                        + "The positive power lower bound on U ensures that these logarithms "
                        + "eventually lie in their positive domains. The gcd is at least one, "
                        + "so U<=N. A positive power lower bound on D makes its double logarithm "
                        + "grow at least as log(log(N)) plus a constant. The power of log(log(log(N))) "
                        + "is smaller than any fixed positive multiple of log(log(N)) eventually.")),
                    Paragraph(Text("The interval condition is the only source-window hypothesis "
                        + "used here. The result does not assert that every pair j,g lies in "
                        + "that interval or that a nonnegative shifted composition is a canonical address."))),
                DescribeRole.Theorem))));

    private static Formula Contract()
    {
        var n = V("N"); var g = V("g"); var r = V("R");
        var alpha = V("alpha"); var beta = V("beta");
        Formula epsilon = Seq(D(1), Minus, D(4), alpha, Minus, D(3), beta);
        Formula delta = Seq(D(1), Minus, D(2), alpha, Minus, D(2), beta);
        Formula cubic = Fr(n, Seq(D(4), P(Seq(Open, P(g, D(2)), Plus, D(1), Close), D(2)), P(r, D(3))));
        return Disp(Seq(V("D"), Gt, cubic, Comma, Sp,
            Open, g, Le, P(n, alpha), Land, Seq(r, Minus, D(1)), Le, P(n, beta), Close,
            Implies, Open, V("D"), Gt, Fr(P(n, epsilon), D(5, 0)), Land,
            V("U"), Ge, Fr(P(n, delta), D(5)), Close, Comma, Sp,
            Forall, V("omega"), Comma, D(0), Lt, V("omega"), Lt, Fr(D(1), D(2)),
            Implies, Exists, V("T"), Comma, Forall, V("j"), Comma, V("g"), Comma, V("r"),
            Comma, Call("hypotheses", V("j"), V("g"), V("r"), alpha, beta), Land,
            n, Ge, V("T"), Implies,
            Call("log", Call("log", Seq(D(2), Plus, V("D")))), Gt,
            P(Call("log", Call("log", Call("log", V("U")))), V("omega"))));
    }
}
