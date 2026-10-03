using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualExteriorEntranceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under the complete conditional source foundations, the actual Cloitre orbit has a least "
        + "even exterior entrance, strict joint clocks and distinct physical rows with macroscopic "
        + "natural caps.",
        H("Actual Cloitre Exterior Entrance"),
        Blocks(
            Paragraph(Text(
                "F is Nat.fib, with F(0)=0 and F(1)=1. C, D, T, X, d and g are the "
                + "unchanged actual finite-prefix construction in CloitreActualRightProfile. "
                + "C(1)=C(2)=1, D(N)=[1,N-1], T(N,x)=N-C(x), X(N,i)=T(N)^i(N-1), "
                + "d(N)=C(N-1), g(N)=X(N,d(N)), and C(N)=C(g(N))+C(N-g(N)) for N>=3. "
                + "The theorem uses precisely this orbit, depth and selected realization. "
                + "G(n)=floor(alpha*(n+1)), with alpha=1/goldenRatio=(sqrt(5)-1)/2. "
                + "On 0<=t<=F(j-2), Q(j,t) is the existing heightDeficit(j,t)=F(j-1)-C(F(j)-t). "
                + "In displays, Hyp31 and Hyp24 abbreviate Hyp31_1 and Hyp24_1. "
                + "periodic(T(N),x) means membership in Function.periodicPts(T(N)).")),
            Node("capBudget", "Literal quadratic cap coefficient", BudgetFormula(),
                "P(j) denotes capBudget(j). At j=9 the value is 13. For j>=10, the "
                + "natural implementation adds 30 before subtracting 3*j; it gives P(10)=21 "
                + "and P(11)=24. The coefficient is used as P=P(k-1), not P(k). "
                + "The source is Recursive descent C.1 at nested-recurrences commit "
                + "d9dbad876c0d3c7b46b692241569fcdf36594344.", DescribeRole.Definition),
            Node("Hyp31_1", "Complete inherited conditional foundations", HypothesisFormula(),
                "Hyp31_1(U) extends the entire Hyp24_1(U), including Hyp21_1(U) and "
                + "SourceFoundations. The ratio seed covers 16384<=n<=131071 with "
                + "22877*C(n)<=15225*n. The golden base covers 1<=n<=65535: G(n)<=C(n), "
                + "and C(n)=G(n) implies "
                + "n=F(j) or F(j)+1 for j>=2, n+1=F(j) for "
                + "odd j>=3, or n in {11,24,25,59}. The small-depth premise covers "
                + "3<=N<=52. All these foundations remain ASSUMED-UNVERIFIED premises; "
                + "this theorem proves no inhabitant of the premise bundle. "
                + "Global positive-index bounds are 1<=C(n) and G(n)<=C(n)<=U(n)<=n. "
                + "U(1)=1, and U(n)=min(n-F(j-2),F(j)) for j>=3 and F(j)<=n<F(j+1). "
                + "U is nondecreasing on positive indices and U(n)<=U(n+1)<=U(n)+1. "
                + "For j>=2, U(F(j))=C(F(j))=G(F(j))=F(j-1); for j>=3, "
                + "C(F(j)+1)=G(F(j)+1)=F(j-1)+1. For q>=6 and every natural t, "
                + "the positive collar [F(q-1),F(q-1)+t] is legal, invariant, captures "
                + "every legal start, and contains every legal periodic point. "
                + "For every N>=3, DepthEntry(N) supplies the least periodic-entry index "
                + "mu<=d(N). Hyp24_1 additionally retains C(F(j)-1)=F(j-1) for j>=5; "
                + "for j>=6 and b<=F(j-1), negative interval invariance and capture in "
                + "[F(j)-b,F(j)] intersect D(F(j+1)-b); and the complete periodic "
                + "intersection max(F(j-1),F(j)-b)<=x<=min(F(j),F(j)+F(j-3)-b). "
                + "The only extensions are the positive-height envelope for j>=9 and "
                + "the anchor descent bound for j>=8, both on the natural closed block. "
                + "The latter is the source Fibonacci collars (1.1) condition. The full "
                + "zero platform Q(j,t)=0 iff t<=platformWidth(j), for j>=8, is reused "
                + "from full24_3. For j>=9, L(j)=floor(2*j/3)-3 equals platformWidth(j); "
                + "the proof applies t<=L(j)+P(j)*Q(j,t) internally and checks L(j)+2<=P(j) "
                + "for all j>=9 to establish L(j)<=P(j) and the positive analytic denominators. "
                + "No monotonicity "
                + "of C, extra finite shelf, free comparison orbit or desired clock "
                + "property is an added premise. The full cited quantitative capture budget "
                + "of section 23.1 and anchor logarithmic theorem of section 24.6 are not "
                + "new Lean conclusions here; this proof uses the inherited negativeCapture "
                + "interface and its own uniform actual-prefix induction.",
                DescribeRole.Definition),
            Node("naturalCap", "Cap of the unique natural Fibonacci block", CapFormula(),
                "For every y>=1, j=Nat.greatestFib(y)>=2 uniquely satisfies "
                + "F(j)<=y<F(j+1). The cap is F(j)-C(y). It differs from the canonical "
                + "golden defect C(y)-G(y). At a Fibonacci anchor F(j), it is not Q(j,0). "
                + "The equality with Q(k,F(k)-y) below applies to the actual counted "
                + "nonanchor rows, whose natural block index is k-1.", DescribeRole.Definition),
            Node("full31_3_statement", "Complete original target proposition", null,
                "This proposition fixes every quantifier and signed terminal coordinate "
                + "of (31.5)-(31.8). It includes actual row injectivity and the cardinality "
                + "of the image of Finset.Ico(1,R). Its analytic inequalities use real "
                + "casts, including F(k-5)>=N/13 with real division. The following "
                + "theorem proves the whole proposition.", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-full31-3"),
                DeclarationHandle.Create(Prefix + "full31_3"),
                H("Least actual exterior entrance, joint clock and physical rows"),
                StatementSource.FromAuthor(TargetFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every U:N->N, natural k>=23 and v<=floor(F(k-4)/2), use the displayed "
                        + "N,A,B,J,sigma,P,L,q,gamma,beta. All arithmetic defining P and L is "
                        + "natural floor arithmetic; alpha,q,gamma,beta and the clock "
                        + "inequalities are real. R, theta and mu are natural; rzero denotes the actual "
                        + "entrance gap. Every a(r) is the signed integer "
                        + "X(N,2*r)-A, including a(R). For 1<=r<R it is positive and equals "
                        + "its natural conversion, so iota(a(r))=C(A+a(r))-B is legal. "
                        + "Every b(r)=A-X(N,2*r+1) is an exact nonnegative subtraction on "
                        + "the proved left-side range, and b(r)<=F(k-3) is the closed "
                        + "domain of Q(k-1).")),
                    Paragraph(Text(
                        "Theta is the first interval-entry time, with membership and "
                        + "exclusion at every earlier index. Mu is separately the least "
                        + "periodic-entry time, with its own leastness condition. The "
                        + "theorem proves theta=2*R, R>=2, and theta<=mu<=d(N). The depth "
                        + "is exactly A-sigma. For v=0 and v=1 the existing zero platform "
                        + "gives sigma=0; the first-pair computation and its domains "
                        + "also cover the maximal allowed v.")),
                    Paragraph(Text(
                        "For every 1<=r<R the same two actual rows satisfy the signed "
                        + "recurrence, contraction and strict reverse affine inequality. "
                        + "All positive a(r) strictly decrease. For 1<=r<R-1 the next "
                        + "deficit exceeds v; at r=R-1 it is at most v, the odd gap is "
                        + "bounded by L+P*v, and a(R-1)<gamma. The actual entrance gap "
                        + "r0=A-X(N,theta)=v-Q(k-1,b(R-1)) lies in [0,v]. At R=2, the "
                        + "earlier stopping range is empty and the last pair is r=1.")),
                    Paragraph(Text(
                        "Y is the image of 1<=r<R under the actual map r->X(N,2*r). "
                        + "That map is injective on this interval, so card(Y)=R-1. "
                        + "Every y is nonanchor and A<y<=A+J<N-1<N. Its natural cap "
                        + "equals Q(k,F(k)-y), and is at least F(k-5), which is at least "
                        + "N/13 over the reals. The same R satisfies R-1>beta and "
                        + "theta>2+2*beta, and each input is used at absolute time "
                        + "2*r<d(N).")),
                    Paragraph(Text(
                        "The proof transports a joint invariant along the actual inner "
                        + "orbit, excludes odd first entry, and reverses exactly R-1 "
                        + "strict affine inequalities from a(R)<=0. The logarithmic "
                        + "bound, signed stopping pair and distinct row count share "
                        + "those witnesses. This is a conditional theorem about natural "
                        + "caps on these physical rows. It gives no canonical-defect, "
                        + "inner-period, or unrestricted algorithm or information lower "
                        + "bound, and makes no equality claim theta=mu."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula? formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("cloitre-actual-exterior-"
                + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula()
                : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Sp, Grp(V(name))), [.. xs]);
    private static Formula Fib(Formula n) => Call("F", n);
    private static Formula Q(Formula j, Formula t) => Call("Q", j, t);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Sp, Grp(x), Grp(y));
    private static Formula Floor(Formula x) => Seq(Lfloor, Sp, x, Sp, Rfloor, Sp);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Less(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula And(params Formula[] xs) =>
        Seq(xs.SelectMany((x, i) => i == 0
            ? new[] { Par(x) } : new[] { Sp, Land, Sp, Par(x) }).ToArray());
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula All(string name, Formula body) =>
        Seq(Forall, Sp, V(name), Comma, Sp, body);
    private static Formula Natural() => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula AlphaValue() => Seq(Alpha, Sp);
    private static Formula GammaValue() => Seq(GammaLower, Sp);
    private static Formula BetaValue() => Seq(Beta, Sp);
    private static Formula ThetaValue() => Seq(Theta, Sp);
    private static Formula SigmaValue() => Seq(SigmaLower, Sp);
    private static Formula MuValue() => Seq(Mu, Sp);
    private static Formula X(Formula i) => Call("X", V("N"), i);
    private static Formula A(Formula r) => Call("a", r);
    private static Formula B(Formula r) => Call("b", r);
    private static Formula Offset(int n) => Sub(V("k"), D((byte)n));
    private static Formula Range(Formula r, Formula end) => And(Leq(D(1), r), Less(r, end));
    private static Formula Denominator() =>
        Add(Add(V("L"), Mul(Par(Sub(V("P"), D(1))), V("v"))), D(1));

    private static Formula BudgetFormula() => Disp(new Formula.Aligned([
        Eqn(Call("P", D(9)), D(1, 3)),
        All("j", Imp(Leq(D(1, 0), V("j")), Eqn(Call("P", V("j")),
            Sub(Add(Floor(Div(new Formula.Power(Par(Sub(V("j"), D(2))), D(2)), D(3))), D(3, 0)),
                Mul(D(3), V("j")))))),
        All("j", Imp(Leq(D(9), V("j")), Eqn(Call("L", V("j")),
            Sub(Floor(Div(Mul(D(2), V("j")), D(3))), D(3)))))
    ]));

    private static Formula HypothesisFormula() => Disp(And(Call("Hyp24", V("U")),
        All("j", All("t", Imp(And(Leq(D(9), V("j")), Leq(D(0), V("t")),
            Leq(V("t"), Fib(Sub(V("j"), D(2))))),
            Imp(Less(D(0), Q(V("j"), V("t"))),
                Leq(V("t"), Mul(Call("P", V("j")), Q(V("j"), V("t")))))))),
        All("j", All("t", Imp(And(Leq(D(8), V("j")), Leq(D(0), V("t")),
            Leq(V("t"), Fib(Sub(V("j"), D(2))))),
            And(Leq(D(0), Q(V("j"), V("t"))),
                Leq(Q(V("j"), V("t")), Floor(Div(Mul(D(2), V("t")), D(3))))))))));

    private static Formula CapFormula() => Disp(All("y", Imp(Leq(D(1), V("y")),
        Eqn(Call("cap", V("y")), Sub(Fib(Call("greatestFib", V("y"))), Call("C", V("y")))))));

    private static Formula TargetFormula()
    {
        var r = V("r");
        var last = Sub(V("R"), D(1));
        var next = Add(r, D(1));
        var twoR = Mul(D(2), r);
        var qr = Q(Offset(1), B(r));
        var qlast = Q(Offset(1), B(last));
        var y = X(twoR);
        var betaArgument = Add(D(1), Div(Mul(Par(Sub(V("P"), AlphaValue())),
            Par(Sub(V("J"), V("v")))), Denominator()));
        var definitions = new Formula.Aligned([
            Eqn(V("N"), Sub(Fib(V("k")), V("v"))),
            Eqn(V("A"), Fib(Offset(1))), Eqn(V("B"), Fib(Offset(2))), Eqn(V("J"), Fib(Offset(4))),
            Eqn(SigmaValue(), Q(V("k"), Add(V("v"), D(1)))),
            Eqn(V("P"), Call("P", Offset(1))), Eqn(V("L"), Call("L", Offset(1))),
            Eqn(AlphaValue(), Div(Sub(Seq(Sqrt, Sp, Grp(D(5))), D(1)), D(2))),
            Eqn(V("q"), Div(V("P"), AlphaValue())),
            Eqn(GammaValue(), Div(Denominator(), AlphaValue())),
            Eqn(BetaValue(), Div(Call("log", betaArgument),
                Call("log", Div(V("P"), AlphaValue())))),
            All("r", Eqn(A(r), Sub(X(twoR), V("A")))),
            All("r", Imp(Range(r, V("R")), Eqn(B(r), Sub(V("A"), X(Add(twoR, D(1)))))))
        ]);
        var first = And(Eqn(Call("d", V("N")), Sub(V("A"), SigmaValue())),
            Leq(D(0), SigmaValue()), Leq(SigmaValue(), V("v")),
            Leq(Add(V("v"), D(1)), V("B")), Leq(Sub(V("v"), SigmaValue()), V("J")),
            Eqn(X(D(1)), Add(Sub(V("B"), V("v")), SigmaValue())),
            Eqn(X(D(2)), Add(V("A"), A(D(1)))),
            Eqn(A(D(1)), Add(Sub(V("J"), V("v")), Q(Offset(2), Sub(V("v"), SigmaValue())))),
            Leq(Sub(V("J"), V("v")), A(D(1))), Leq(A(D(1)), V("J")));
        var paired = All("r", Imp(Range(r, V("R")), And(
            Leq(D(1), A(r)), Leq(A(r), V("J")),
            Eqn(B(r), Add(V("v"), Call("iota", A(r)))),
            Eqn(Call("iota", A(r)), Sub(Call("C", Add(V("A"), A(r))), V("B"))),
            Less(V("v"), B(r)), Leq(B(r), Add(V("v"), V("J"))),
            Leq(Add(V("v"), V("J")), Fib(Offset(3))),
            Eqn(X(Add(twoR, D(1))), Sub(V("A"), B(r))),
            Eqn(A(next), Sub(qr, V("v"))),
            Leq(Mul(D(3), A(next)), Sub(Mul(D(2), A(r)), V("v"))),
            Less(A(r), Add(Mul(V("q"), A(next)), GammaValue())))));
        var stopping = And(Leq(Sub(D(0), V("v")), A(V("R"))), Leq(A(V("R")), D(0)),
            All("r", Imp(Range(r, last), Less(V("v"), qr))),
            Leq(qlast, V("v")), Less(V("v"), B(last)),
            Leq(B(last), Add(V("L"), Mul(V("P"), V("v")))), Less(A(last), GammaValue()),
            Eqn(V("rzero"), Sub(V("A"), X(ThetaValue()))),
            Eqn(V("rzero"), Sub(V("v"), qlast)), Leq(D(0), V("rzero")), Leq(V("rzero"), V("v")));
        var rows = And(
            Eqn(V("Y"), Seq(OpenBrace, Sp, X(twoR), Sp, Mid, Sp, Range(r, V("R")), Sp, CloseBrace)),
            All("r", All("s", Imp(And(Range(r, V("R")), Range(V("s"), V("R")), Less(r, V("s"))),
                Less(A(V("s")), A(r))))),
            All("r", All("s", Imp(And(Range(r, V("R")), Range(V("s"), V("R")),
                Eqn(X(twoR), X(Mul(D(2), V("s"))))), Eqn(r, V("s"))))),
            Eqn(Seq(Lvert, Sp, V("Y"), Sp, Rvert, Sp), last),
            All("r", Imp(Range(r, V("R")), And(
                All("j", Imp(Leq(D(2), V("j")), Seq(y, Sp, Neq, Sp, Fib(V("j"))))),
                Less(V("A"), y), Leq(y, Add(V("A"), V("J"))),
                Less(Add(V("A"), V("J")), Sub(V("N"), D(1))), Less(Sub(V("N"), D(1)), V("N")),
                Eqn(Call("cap", y), Q(V("k"), Sub(Fib(V("k")), y))),
                Leq(Fib(Offset(5)), Call("cap", y)), Leq(Div(V("N"), D(1, 3)), Fib(Offset(5))),
                Less(twoR, Call("d", V("N")))))));
        var clocks = And(Leq(D(2), V("R")), Eqn(ThetaValue(), Mul(D(2), V("R"))),
            Leq(Sub(V("A"), V("v")), X(ThetaValue())), Leq(X(ThetaValue()), V("A")),
            All("i", Imp(Less(V("i"), ThetaValue()),
                Seq(Neg, Sp, Par(And(Leq(Sub(V("A"), V("v")), X(V("i"))),
                    Leq(X(V("i")), V("A"))))))),
            Call("periodic", Call("T", V("N")), X(MuValue())),
            All("i", Imp(Less(V("i"), MuValue()),
                Seq(Neg, Sp, Call("periodic", Call("T", V("N")), X(V("i")))))),
            Leq(ThetaValue(), MuValue()), Leq(MuValue(), Call("d", V("N"))),
            Less(BetaValue(), last), Less(Add(D(2), Mul(D(2), BetaValue())), ThetaValue()));
        return Disp(Seq(All("U", Imp(Call("Hyp31", V("U")),
            All("k", All("v", Imp(And(Leq(D(2, 3), V("k")), Leq(D(0), V("v")),
                Leq(V("v"), Floor(Div(Fib(Offset(4)), D(2))))),
                Seq(Exists, Sp, V("R"), Comma, Sp, ThetaValue(), Comma, Sp, MuValue(),
                    Colon, Sp, Natural(), Comma, Sp,
                    And(definitions, clocks, first, paired, stopping, rows)))))))));
    }
}
