using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233260LiteralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.";
    private const string OriginalName = "Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).";
    private const string OriginalFormula = "Empirical: a(n) = 512*a(n-1) -65536*a(n-2) +2490368*a(n-3) +17825792*a(n-4) -2818572288*a(n-5) +51539607552*a(n-6) -274877906944*a(n-7) for n>11";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233260");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal five-row complementary-pair arrays with horizontal and antidiagonal bonds.",
        H("Five-row antidiagonal arrays"), Blocks(
            Paragraph(Text("An array is a function from Fin 5 times Fin n to Fin 6. "
                + "A bond joins (r,j) to (s,j+1) exactly when r=s or r.val=s.val+1. "
                + "It excludes equal colours and colours whose values sum to five. "
                + "The first entry is zero. The rank r.val*n+j.val defines the strict "
                + "row-major predecessor relation. No colour is required to occur.")),
            Node("normal", "Strict row-major normalization", NormalFormula(), false, true),
            Node("Legal", "Literal array predicate", LegalFormula(), false, true),
            Node("a", "Literal finite count", CountFormula(), false, true),
            Node("Proper", "Proper pair-label pattern", ProperFormula(), false, false),
            Node("L", "Labelled three-colour count", LabelCountFormula(), false, false),
            Node("columns_constant", "Omitting a label forces constant columns",
                ColumnsConstantFormula(), true, false),
            Node("counting_bridge", "Exact complementary-pair count", BridgeFormula(), true, false),
            Paragraph(Text("The pair labels identify {0,5}, {1,4}, and {2,3}. "
                + "Canonical first occurrences fix the pair names and the first side "
                + "of each used pair. A pattern with k used pairs has 2^(5*n-k) lifts. "
                + "At width at least two, every proper pattern uses two or three labels, "
                + "and every orbit under label permutations has six members. When one "
                + "label is omitted, the common neighbours of consecutive rows force "
                + "each column to be constant, including the last column. The two "
                + "remaining labels alternate with column parity. Exactly one such "
                + "pattern is canonical. Summing the two possible lift weights gives "
                + "the displayed identity.")),
            Node("result", "The seven-lag integer recurrence", RecurrenceFormula(), true, true),
            Paragraph(Text("Column states record five independent pair labels. Relabelling "
                + "reduces their transitions to forty-one classes. The transfer polynomial is "
                + "x^7-16*x^6+64*x^5-76*x^4-17*x^3+84*x^2-48*x+8. Its vector relation "
                + "holds after four transitions and its value at one is zero. The scalar "
                + "relation covers every index at least thirteen; the same finite power "
                + "table verifies index twelve. The counting bridge scales each lag "
                + "coefficient by a power of thirty-two. Every count used has positive "
                + "width. The final statement quantifies all integers greater than eleven.")))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature && !theorem ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(literature
                ? "OEIS A233260, revision 7, " + (name == "result" ? "FORMULA: " + OriginalFormula : "NAME: " + OriginalName)
                : title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hardin233260"), ResolutionKind.Proved) : null);
    private static Formula ColumnsConstantFormula()
    {
        var n = V("n"); var p = V("P"); var d = V("d");
        var j = V("j"); var r = V("r"); var i = V("i");
        var cells = Product(Fin(D(5)), Fin(n));
        var omitted = All("i", cells, Ne(App(p, i), d));
        var constant = All("j", Fin(n), All("r", Fin(D(5)),
            Eq(App(p, Pair(r, j)), App(p, Pair(Typed(D(0), Fin(D(5))), j)))));
        var pattern = All("P", Arrow(cells, Fin(D(3))), Imp(Own("Proper", p),
            All("d", Fin(D(3)), Imp(omitted, constant))));
        return All("n", Q("Nat"), Imp(Le(D(2), n), pattern));
    }
    private static Formula BridgeFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Le(D(2), n), Eq(
            Mul(D(4,8), Typed(Own("a", n), Q("Int"))),
            Mul(Power(Typed(D(3,2), Q("Int")), n),
                Add(Typed(Own("L", n), Q("Int")), D(6))))));
    }
    private static Formula ProperFormula()
    {
        var n=V("n"); var p=V("P"); var j=V("j"); var h=V("h"); var r=V("r"); var s=V("s");
        var cells=Product(Fin(D(5)),Fin(n));
        var adjacent=Or(Eq(r,s),Eq(Val(r),Add(Val(s),D(1))));
        var next=Typed(Call("Fin.mk",Add(Val(j),D(1)),h),Fin(n));
        var bonds=All("j",Fin(n),All("h",Lt(Add(Val(j),D(1)),n),
            All("r",Fin(D(5)),All("s",Fin(D(5)),Imp(adjacent,Ne(App(p,Pair(r,j)),App(p,Pair(s,next))))))));
        return All("n",Q("Nat"),All("P",Arrow(cells,Fin(D(3))),Eq(Own("Proper",p),Parenthesized(bonds))));
    }
    private static Formula LabelCountFormula()
    {
        var n=V("n"); var p=V("P"); var arrays=Arrow(Product(Fin(D(5)),Fin(n)),Fin(D(3)));
        return All("n",Q("Nat"),Eq(Own("L",n),Call("Finset.card",
            Call("Finset.filter",Fn("P",arrays,Own("Proper",p)),Q("Finset.univ")))));
    }
    private static Formula RecurrenceFormula()
    {
        var n=V("n");
        Formula A(int k) => Typed(Own("a",Call("Int.toNat",k==0 ? n : Sub(n,Num(k)))),Q("Int"));
        var rhs=Sub(Add(Sub(Add(Add(Sub(Mul(Num(512),A(1)),Mul(Num(65536),A(2))),
            Mul(Num(2490368),A(3))),Mul(Num(17825792),A(4))),Mul(Num(2818572288),A(5))),
            Mul(Num(51539607552),A(6))),Mul(Num(274877906944),A(7)));
        return All("n",Q("Int"),Imp(Lt(Num(11),n),Eq(A(0),rhs)));
    }

    private static Formula NormalFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q");
        var cells = Product(Fin(D(5)), Fin(n));
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
        var cells = Product(Fin(D(5)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(5))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = Or(Eq(r, s), Eq(Val(r), Add(Val(s), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(5)), All("s", Fin(D(5)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("Legal", a), Parenthesized(And(first, And(bonds, Own("normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(5)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)), Q("Finset.univ")))));
    }

    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
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
