using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233179LadderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.";

    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233179");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's order-24 recurrence for normalized six-row complementary-pair ladders.",
        H("Six-row complementary-pair ladders"), Blocks(
            Paragraph(Text("Cells are Fin 6 times Fin n and colours are Fin 6. "
                + "Bonds join consecutive columns at row distance at most one; within-column "
                + "entries are unconstrained. The first cell is zero. Predecessors are "
                + "ordered by row.val*n+column.val.")),
            Node("normal", "Row-major predecessor conditions", NormalFormula(), false),
            Node("Legal", "Literal array conditions", LegalFormula(), false),
            Node("a", "The literal filtered count", CountFormula(), false, true),
            Node("counting_bridge", "The pair-pattern counting bridge", BridgeFormula(), true),
            Paragraph(Text("The canonical-form theorems apply to the row-major cell "
                + "order without changing their definitions. A canonical pair pattern using "
                + "k labels has 2^(6*n-k) colour lifts. Proper patterns at width at least two "
                + "use two or three labels, and each orbit has six members. If only two labels "
                + "occur, HardinA233177Ladder.two_label_classification applies to the four-row "
                + "windows 0–3 and 2–5. Their restrictions inherit Proper and the omitted "
                + "label by argument substitution. Shared row 2 at columns 0 and 1 identifies "
                + "both alternating labels, so the restrictions combine coordinatewise. "
                + "Exactly one such pattern "
                + "is canonical. Thus, if C is the canonical-pattern count, L=6*C and "
                + "a=2^(6*n-3)*(C+1), giving the displayed bridge.")),
            Node("finite_certificate", "The recurrence at width 26", RecurrenceFormula(null), true),
            Resolution("result", "Hardin's shifted integer recurrence", RecurrenceFormula(V("n"))),
            Paragraph(Text("For an ordered partition into k pair blocks the first cell of each block "
                + "has its lower colour fixed, leaving 6n−k free signs and 2^(6n−k) lifts. "
                + "At width two a two-block partition has 1024 lifts. In degree one the "
                + "one-block partition has 32 lifts. "
                + "For n≥2 the counting bridge has the common algebraic factor 2^(6n)=64^n "
                + "in 48a(n)=64^n(L(n)+6). The ratio of the factors at widths n and n−j "
                + "is 64^j, which scales the coefficient at lag j. "
                + "The finite instance supplies width 26 and the shifted transfer relation "
                + "supplies every width n≥27. The index n+26 expresses exactly the "
                + "published range index>25.")),
            Paragraph(Text("For every positive width n, a(n) is T(6,n) for the diagonal "
                + "strip. The row-major bijection sends cell (r,j) to r*n+j and its "
                + "inverse reconstructs the array. It preserves the first cell, both "
                + "predecessor conditions and the complementary-pair bond predicate. "
                + "HardinThinGraphTransport.literalEquiv identifies these same arrays "
                + "with normalized colourings of the ordered strip graph.")),
            Paragraph(Text("The width-one strip is edgeless. The complete graph formula "
                + "from HardinGraphNormalization.total_identity then gives "
                + "48*T(h,1)=6^h+3*4^h+15*2^h for every positive h, by counting all "
                + "functions into palettes of sizes three, two and one. At h=6 this "
                + "gives a(1)=1248. The counting bridge and "
                + "HardinA233179PairTransfer.initial_values give a(2)=124928, "
                + "a(3)=127533056 and a(4)=82428559360. "
                + "HardinColumnPolynomials.sixRow_walk and rowSix supply the separate "
                + "continuation interpretation and the full vector relation on all "
                + "729 actual columns, together with the coefficient sum one.")),
            Paragraph(Text("For the ordinary generating series set a(0)=b(0)=0 in "
                + "degree zero, take b(1)=936, and use b(n)=L(n)+6 for every n at "
                + "least two. Then the integer identity 48*a(n)=64^n*b(n) holds "
                + "coefficientwise. Let c(j) be the lag-j coefficient before scaling, "
                + "so q(t)=1-sum(c(j)*t^j, j=1..24). In degree n the coefficient "
                + "of q(t) times the series with coefficients b(n) is "
                + "b(n)-sum(c(j)*b(n-j), j=1..min(n,24)).")),
            Paragraph(Text("The coefficients of this product in exponents 0 through 25 "
                + "are (0, 936, -5088, -83304, 263214, 2175108, -5145426, "
                + "-23138070, 53133882, 111863904, -292206522, -225606702, "
                + "823430316, 104406570, -1226356254, 236624820, 1000188192, "
                + "-361101846, -449345922, 201432990, 107989830, -52135680, "
                + "-12870528, 6171630, 580770, -267300). The zero constant comes "
                + "from b(0). The positive-degree entries use the edgeless b(1) "
                + "and the proved initial values of L. In every degree n at least "
                + "26, multiply the convolution by 64^n to obtain 48 times the "
                + "literal recurrence residual. The result theorem makes it zero "
                + "including at degree 26, so cancellation gives a polynomial R "
                + "with exactly the displayed coefficients.")),
            Paragraph(Text("Over the rationals, formal rescaling takes the coefficient "
                + "in degree n to 64^n times that coefficient and preserves products. "
                + "The constant coefficient of 48*q(64*z) is 48, so it is a unit. "
                + "The series with coefficient a(n) in every positive degree and "
                + "zero constant is therefore R(64*z)/(48*q(64*z)).")),
            Paragraph(Text("In degree 25 all 24 lags occur and the last uses the actual "
                + "width-one count. The literal residual is "
                + "64^25*(-267300)/48 = -22275*2^148, which is nonzero. Thus "
                + "26 is the sharp onset for these specified coefficients.")))));

    private static DocumentBlock Resolution(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233179"),
                ResolutionKind.Proved));

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem,
        bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula BridgeFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Le(D(2), n), Eq(
            Mul(D(4,8), Typed(Own("a", n), Q("Int"))),
            Mul(Power(Typed(D(6,4), Q("Int")), n),
                Add(Typed(Call("D5.S3.Combinatorics.TraceAvoidingArrays."
                    + "HardinA233179PairTransfer.L", n), Q("Int")), D(6))))));
    }

    private static Formula RecurrenceFormula(Formula? n)
    {
        Formula A(int i) => Typed(Own("a", n is null ? Num(i) : Add(n, Num(i))), Q("Int"));
        Formula rhs = Mul(N("448"), A(25));
        rhs = Add(rhs, Mul(N("421888"), A(24)));
        rhs = Sub(rhs, Mul(N("95682560"), A(23)));
        rhs = Sub(rhs, Mul(N("48586817536"), A(22)));
        rhs = Add(rhs, Mul(N("7696581394432"), A(21)));
        rhs = Add(rhs, Mul(N("2219020623282176"), A(20)));
        rhs = Sub(rhs, Mul(N("331924968239529984"), A(19)));
        rhs = Sub(rhs, Mul(N("45544058606667694080"), A(18)));
        rhs = Add(rhs, Mul(N("7676565708838105251840"), A(17)));
        rhs = Add(rhs, Mul(N("384720682715267981115392"), A(16)));
        rhs = Sub(rhs, Mul(N("90389119748153097756606464"), A(15)));
        rhs = Sub(rhs, Mul(N("732939612340266155036901376"), A(14)));
        rhs = Add(rhs, Mul(N("559176850836005482125888323584"), A(13)));
        rhs = Sub(rhs, Mul(N("7028965514623047698676841447424"), A(12)));
        rhs = Sub(rhs, Mul(N("1887473560557987165955670813966336"), A(11)));
        rhs = Add(rhs, Mul(N("44169859058027396737075939400220672"), A(10)));
        rhs = Add(rhs, Mul(N("3500683050361467360162023730212503552"), A(9)));
        rhs = Sub(rhs, Mul(N("101555160700421718306247628235154128896"), A(8)));
        rhs = Sub(rhs, Mul(N("3466958920006006825501354764976208740352"), A(7)));
        rhs = Add(rhs, Mul(N("108207134224866861549607317549181730553856"), A(6)));
        rhs = Add(rhs, Mul(N("1701156622829501613469275506203267231121408"), A(5)));
        rhs = Sub(rhs, Mul(N("52659376845749069097884147249280994259238912"), A(4)));
        rhs = Sub(rhs, Mul(N("315694924216699133847365011797178367569035264"), A(3)));
        rhs = Add(rhs, Mul(N("9366312983382861719445001674512311832511774720"), A(2)));
        var equation = Eq(A(26), rhs);
        return n is null ? equation : All("n", Q("Nat"), equation);
    }

    private static Formula NormalFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q");
        var cells = Product(Fin(D(6)), Fin(n));
        Formula Rank(Formula x) => Add(Mul(Val(Call("Prod.fst", x)), n),
            Val(Call("Prod.snd", x)));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), Typed(D(colour), Fin(D(6))))));
        var current = App(a, p);
        var condition = All("p", cells, And(
            Imp(Or(Eq(current, Typed(D(2), Fin(D(6)))),
                Or(Eq(current, Typed(D(3), Fin(D(6)))),
                    Eq(current, Typed(D(4), Fin(D(6)))))), Earlier(1)),
            Imp(Eq(current, Typed(D(3), Fin(D(6)))), Earlier(2))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("normal", a), Parenthesized(condition))));
    }

    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j");
        var r = V("r"); var s = V("s"); var h = V("h");
        var cells = Product(Fin(D(6)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(6))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = And(Le(Val(r), Add(Val(s), D(1))),
            Le(Val(s), Add(Val(r), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(6)), All("s", Fin(D(6)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("Legal", a), Parenthesized(And(first, And(bonds, Own("normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(6)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)), Typed(Q("Finset.univ"), Call("Finset", arrays))))));
    }

    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula N(string digits) => D(digits.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
