using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233164KingStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233164");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full generating series of normalized four-column eight-colour king strips.",
        H("Horizontal, vertical and both diagonal exclusions"),
        Blocks(
            Paragraph(Text("OEIS A233164, revision 8, defines literal n by four arrays with colours zero through seven. Every horizontal, vertical and both diagonal bonds exclude equal colours and colours summing to seven. There is no wraparound. The upper-left value is zero. Every occurrence of 2, 3, 4, 5 or 6 has a strictly earlier 1; every 3, 4 or 5 has a strictly earlier 2; every 4 has a strictly earlier 3, in row-major order. Colours may be absent, and no precedence condition is imposed on 7. No group action or orbit divisor enters the count.")),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "a"),
                H("An independent literal count"), StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Finset.univ ranges over every function on the displayed finite cell domain. Fin.val gives the natural coordinate. Fin.castSucc and Fin.succ are the two endpoints in adjacent columns; Fin.mk constructs the next row with its displayed bound proof. The rank 4 times row plus column is strictly row-major. The first-cell existential is false when n is zero, so the added constant coefficient is zero. The source counting problem concerns every positive n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-row"), DeclarationHandle.Create(Prefix + "Row"),
                H("Row"), StatementSource.FromAuthor(Disp(ApiFormula("Row"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Signed colours on the ordered row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-boundary"), DeclarationHandle.Create(Prefix + "Boundary"),
                H("Boundary"), StatementSource.FromAuthor(Disp(ApiFormula("Boundary"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Complementary-pair colours on the same row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-rowlegal"), DeclarationHandle.Create(Prefix + "rowLegal"),
                H("rowLegal"), StatementSource.FromAuthor(Disp(ApiFormula("rowLegal"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Adjacent signed colours exclude equality and complementarity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-pairs"), DeclarationHandle.Create(Prefix + "pairs"),
                H("pairs"), StatementSource.FromAuthor(Disp(ApiFormula("pairs"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The pair map is applied in each column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-compatible"), DeclarationHandle.Create(Prefix + "compatible"),
                H("compatible"), StatementSource.FromAuthor(Disp(ApiFormula("compatible"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Vertical and both diagonal pair colours differ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-step"), DeclarationHandle.Create(Prefix + "step"),
                H("step"), StatementSource.FromAuthor(Disp(ApiFormula("step"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The scanner-weighted sum ranges over every signed next row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-saturated"), DeclarationHandle.Create(Prefix + "saturated"),
                H("saturated"), StatementSource.FromAuthor(Disp(ApiFormula("saturated"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("All three precedence flags are true."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-proper"), DeclarationHandle.Create(Prefix + "proper"),
                H("proper"), StatementSource.FromAuthor(Disp(ApiFormula("proper"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The productive pair-boundary predicate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-kind"), DeclarationHandle.Create(Prefix + "kind"),
                H("kind"), StatementSource.FromAuthor(Disp(ApiFormula("kind"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The alternating equality pattern determines the two rates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-rate"), DeclarationHandle.Create(Prefix + "rate"),
                H("rate"), StatementSource.FromAuthor(Disp(ApiFormula("rate"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The signed continuation count is integer valued."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("api-saturated-certificate"), DeclarationHandle.Create(Prefix + "saturated_certificate"),
                H("saturated_certificate"), StatementSource.FromAuthor(Disp(ApiFormula("saturated_certificate"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Every admissible signed continuation preserves saturation, properness and kind; the unweighted sum equals the displayed rate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The complete rational formal power series"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The complementary pairs are {0,7}, {1,6}, {2,5} and {3,4}. A pair boundary with adjacent entries distinct is productive precisely when its endpoints differ. Its alternating type has first equal to third and second equal to fourth. Once 1, 2 and 3 have appeared, every legal next row preserves the productive type, with 32 colour-row continuations in the alternating type and 16 otherwise. The finite certificates verify these counts, preservation, and saturation of every two-row seed. There are 16 alternating seeds and 48 other productive seeds. The continuation induction gives a(n+2)=16 times 32 to the n plus 48 times 16 to the n for every natural n. There are 11 first rows.")),
                    Paragraph(Text("The literal Normal predicate uses strict rank 4 times row plus column. Its equivalence with the imported scanner and the arbitrary-width width_counting_bridge connects the independently defined function count to continuation. Both diagonal directions, vertical bonds and horizontal bonds are included, and boundaries are free. The initial values, natural closed form, integer recurrence and rational series are one conjunction about this count. The constant coefficient is zero solely for the series. The inverse denominator has constant coefficient one. Chang and Shrock already give the labelled proper-colouring polynomial for these underlying strips, DOI 10.1103/PhysRevE.62.4650; that polynomial is not a new result here. The normalized literal count requires the signed-lift and first-occurrence constraints stated above."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233164"),
                    ResolutionKind.Proved)))));

    private static Formula ApiFormula(string name)
    {
        var c = V("c"); var p = V("p"); var j = V("j"); var w = V("w"); var t = V("t");
        var row = Arrow(Fin(4), Fin(8)); var boundary = Arrow(Fin(4), Fin(4));
        var seen = Product(V("Bool"), Product(V("Bool"), V("Bool")));
        var left = Call("Fin.castSucc", j); var right = Call("Fin.succ", j);
        Formula PairColour(Formula a) => Call("HardinA233196Strip.beta", App(c, a));
        var legal = All("j", Fin(3), And(Ne(App(c,left),App(c,right)), Ne(Add(Val(App(c,left)),Val(App(c,right))),D(7))));
        var compat = And(All("j", Fin(4), Ne(App(p,j),PairColour(j))),
            All("j", Fin(3), And(Ne(App(p,left),PairColour(right)),Ne(App(p,right),PairColour(left)))));
        var prop = And(All("j",Fin(3),Ne(App(p,left),App(p,right))),Ne(App(p,D(0)),App(p,D(3))));
        var kind = And(Eq(App(p,D(0)),App(p,D(2))),Eq(App(p,D(1)),App(p,D(3))));
        var pred = And(Call("rowLegal",c), And(Call("compatible",p,c), Call("HardinA233196Strip.good",Call("saturated"),c)));
        return name switch
        {
            "Row" => Eq(Call("Row"),row),
            "Boundary" => Eq(Call("Boundary"),boundary),
            "rowLegal" => All("c",row,Iff(Call("rowLegal",c),legal)),
            "pairs" => All("c",row,All("j",Fin(4),Eq(App(Call("pairs",c),j),PairColour(j)))),
            "compatible" => All("p",boundary,All("c",row,Iff(Call("compatible",p,c),compat))),
            "saturated" => Eq(Call("saturated"),Pair(V("true"),Pair(V("true"),V("true")))),
            "proper" => All("p",boundary,Iff(Call("proper",p),prop)),
            "kind" => All("p",boundary,Eq(Call("kind",p),Call("decide",Parenthesized(kind)))),
            "rate" => All("b",V("Bool"),Eq(Call("rate",V("b")),Conditional(Eq(V("b"),V("true")),Typed(D(3,2),V("Int")),Typed(D(1,6),V("Int"))))),
            "step" => All("w",Arrow(seen,Arrow(boundary,V("Int"))),All("t",seen,All("p",boundary,
                Eq(Call("step",w,t,p),SumOver("c",row,Conditional(And(Call("rowLegal",c),And(Call("compatible",p,c),Call("HardinA233196Strip.good",t,c))),
                    App(w,Call("HardinA233196Strip.finish",t,c),Call("pairs",c)),Typed(D(0),V("Int")))))))),
            _ => All("p",boundary,Imp(Call("proper",p),And(All("c",row,Imp(pred,
                And(Eq(Call("HardinA233196Strip.finish",Call("saturated"),c),Call("saturated")),
                    And(Call("proper",Call("pairs",c)),Eq(Call("kind",Call("pairs",c)),Call("kind",p)))))),
                Eq(Call("step",Call("Function.const",seen,Call("Function.const",boundary,Typed(D(1),V("Int")))),Call("saturated"),p),Call("rate",Call("kind",p))))))
        };
    }

    private static Formula Typed(Formula f, Formula t) => Parenthesized(Seq(f,Colon,Sp,t));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a),Sp,F.Iff,Sp,Parenthesized(b));
    private static Formula Conditional(Formula p, Formula y, Formula n) => Parenthesized(Seq(Name("if"),Sp,Parenthesized(p),Sp,Name("then"),Sp,y,Sp,Name("else"),Sp,n));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(b));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var h = V("h"); var p = V("p"); var q = V("q");
        var cells = Product(Call("Fin", n), Fin(4));
        Formula Cell(Formula r, Formula c) => App(a, Pair(r, c));
        Formula Bond(Formula u, Formula v) => And(Ne(u, v), Ne(Add(Val(u), Val(v)), D(7)));
        var left = Call("Fin.castSucc", j); var right = Call("Fin.succ", j);
        var next = Call("Fin.mk", Add(Val(i), D(1)), h);
        var first = Ex("i", Call("Fin", n), And(Eq(Val(i), D(0)), Eq(Cell(i, D(0)), D(0))));
        var horizontal = All("i", Call("Fin", n), All("j", Fin(3), Bond(Cell(i, left), Cell(i, right))));
        var diagonal = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), D(1)), n),
            All("j", Fin(3), And(Bond(Cell(i, left), Cell(next, right)),
                Bond(Cell(i, right), Cell(next, left))))));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), D(colour))));
        var vertical = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), D(1)), n),
            All("j", Fin(4), Bond(Cell(i, j), Cell(next, j)))));
        var normal = All("p", cells, And(
            Imp(Or(Eq(App(a, p), D(2)), Or(Eq(App(a, p), D(3)),
                Or(Eq(App(a, p), D(4)), Or(Eq(App(a, p), D(5)), Eq(App(a, p), D(6)))))), Earlier(1)),
            And(Imp(Or(Eq(App(a, p), D(3)), Or(Eq(App(a, p), D(4)), Eq(App(a, p), D(5)))), Earlier(2)),
                Imp(Eq(App(a, p), D(4)), Earlier(3)))));
        var predicate = Seq(LambdaLower, Sp, a, Colon, Sp, Arrow(cells, Fin(8)), Sp,
            Mapsto, Sp, Parenthesized(And(first, And(horizontal, And(And(vertical, diagonal), normal)))));
        return All("n", V("Nat"), Eq(Call("a", n),
            Call("Finset.card", Call("Finset.filter", predicate, Call("Finset.univ")))));
    }

    private static Formula ResultFormula()
    {
        var x = V("X"); var n = V("n");
        Formula A(Formula k) => Call("a", k);
        var series = Call("PowerSeries.mk", Seq(LambdaLower, Sp, n, Colon, Sp, V("Nat"), Sp,
            Mapsto, Sp, Parenthesized(Seq(A(n), Colon, Sp, V("Rat")))));
        var numerator = Mul(x, Add(Sub(D(1,1), Mul(D(4,6,4), x)), Mul(D(3,8,4,0), Pow(x, D(2)))));
        var denominator = Mul(Sub(D(1), Mul(D(1,6), x)), Sub(D(1), Mul(D(3,2), x)));
        var gf = Seq(Eq(series, Mul(numerator, Pow(Parenthesized(denominator), new Formula.Negate(Num(1))))),
            Sp, Name("in"), Sp, Call("PowerSeries", V("Rat")));
        var closed = All("n", V("Nat"), Imp(Lt(D(1), n),
            Eq(A(n), Mul(Pow(D(4), Sub(Mul(D(2), n), D(3))), Add(Pow(D(2), n), D(1,2))))));
        var recurrence = All("n", V("Nat"), Imp(Lt(D(3), V("n")), Eq(Typed(A(V("n")), V("Int")), Sub(Mul(D(4, 8), Call("Int.ofNat", A(Sub(V("n"), D(1))))), Mul(D(5, 1, 2), Call("Int.ofNat", A(Sub(V("n"), D(2)))))))));
        return And(Eq(A(D(1)),D(1,1)), And(Eq(A(D(2)),D(6,4)),
            And(Eq(A(D(3)),D(1,2,8,0)), And(closed,And(recurrence,gf)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Rank(Formula p) => Add(Mul(D(4), Val(Call("Prod.fst", p))), Val(Call("Prod.snd", p)));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
}
