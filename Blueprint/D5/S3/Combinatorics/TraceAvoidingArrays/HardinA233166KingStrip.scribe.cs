using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233166KingStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal six-column king strips and complementary-pair zones.",
        H("Strict normalization and four-colour rectangle structure"),
        Blocks(
            Paragraph(Text("OEIS A233166, revision 8, NAME: Number of n X 6 0..7 arrays with no element x(i,j) adjacent to itself or value 7-x(i,j) horizontally, diagonally, antidiagonally or vertically, top left element zero, and 1 appearing before 2 3 4 5 and 6, 2 appearing before 3 4 and 5, and 3 appearing before 4 in row major order (unlabelled 8-colorings with no clashing color pairs).")),
            Describe.Lean(DescribeId.Create("legal"), DeclarationHandle.Create(Prefix + "Legal"),
                H("Literal functions with free boundaries"), StatementSource.FromAuthor(Disp(LegalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Both coordinate inequalities in both directions mean absolute difference at most one. The distinctness condition excludes the same cell. The rank is six times the row plus the column, and every earlier-cell inequality is strict. All functions are counted themselves. Colours may be absent; seven has no further precedence condition. The first-cell existential is false at height zero. Fin.val supplies coordinate values."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "a"),
                H("The literal cardinality"), StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Finset.univ ranges over every function on Fin n times Fin 6 into Fin 8. There is no group quotient, orbit divisor, transposition or boundary identification. The zero constant coefficient extends the positive-height source sequence only for its formal generating series."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The complete conjectural conjunction"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("FORMULA: Empirical: a(n) = 192*a(n-1) - 8192*a(n-2) for n>3. Conjectures from _Colin Barker_, Oct 09 2018: (Start) G.f.: 4*x*(59 - 10304*x + 356352*x^2) / ((1 - 64*x)*(1 - 128*x)). a(n) = 64^(n-1) * (2^n+60) for n>1. (End). The first DATA entry is 236. This proposition includes that exceptional value and every universal onset. PowerSeries.mk uses rational casts of the actual counts. The displayed denominator has constant coefficient one, so its formal inverse exists uniquely. The rectangle theorem below does not prove this conjunction: the signed normalization fibres and their counts remain to be established."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rectangle"), DeclarationHandle.Create(Prefix + "pair_rectangle"),
                H("Necessary zone data for every literal strip"), StatementSource.FromAuthor(Disp(RectangleFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Write c(i,j)=beta(f(i,j)), where beta identifies the complementary pairs {0,7}, {1,6}, {2,5}, {3,4}. The binary operation xor is bitwise exclusive-or on Fin 4. Every adjacent square has four distinct pair colours. The xor of its upper edge equals that of its lower edge, and likewise for its left and right edges. Induction along rows and columns gives the displayed reconstruction. Horizontal and vertical increments are nonzero, and every horizontal increment differs from every vertical increment because the antidiagonal cells are adjacent. The first square also contains all four pair colours. Strict precedence then forces the literal colours one, two and three to have appeared within the first two rows. The zone correspondence is the algebraic rectangular form of Eppstein's published kinggraph construction. This statement concerns the original literal functions and does not replace their count with a labelled count."))),
                DescribeRole.Theorem))));

    private static Formula LegalFormula()
    {
        var n=V("n"); var f=V("f"); var p=V("p"); var q=V("q");
        var cells=Product(Call("Fin",n),Fin(6));
        Formula At(Formula r) => App(f,r);
        Formula Coord(Formula r, string name) => Val(Call(name,r));
        var adjacent=And(Ne(p,q),And(
            Le(Coord(p,"Prod.fst"),Add(Coord(q,"Prod.fst"),D(1))),And(
            Le(Coord(q,"Prod.fst"),Add(Coord(p,"Prod.fst"),D(1))),And(
            Le(Coord(p,"Prod.snd"),Add(Coord(q,"Prod.snd"),D(1))),
            Le(Coord(q,"Prod.snd"),Add(Coord(p,"Prod.snd"),D(1)))))));
        var bonds=All("p",cells,All("q",cells,Imp(adjacent,
            And(Ne(At(p),At(q)),Ne(Add(Val(At(p)),Val(At(q))),D(7))))));
        Formula Earlier(byte k) => Ex("q",cells,And(Lt(Rank(q),Rank(p)),Eq(At(q),D(k))));
        var normal=All("p",cells,And(
            Imp(Or(Eq(At(p),D(2)),Or(Eq(At(p),D(3)),Or(Eq(At(p),D(4)),Or(Eq(At(p),D(5)),Eq(At(p),D(6)))))),Earlier(1)),
            And(Imp(Or(Eq(At(p),D(3)),Or(Eq(At(p),D(4)),Eq(At(p),D(5)))),Earlier(2)),
                Imp(Eq(At(p),D(4)),Earlier(3)))));
        var first=Ex("i",Call("Fin",n),And(Eq(Val(V("i")),D(0)),Eq(At(Pair(V("i"),D(0))),D(0))));
        return All("n",V("Nat"),All("f",Arrow(cells,Fin(8)),
            Iff(Call("Legal",f),And(first,And(bonds,normal)))));
    }

    private static Formula CountFormula()
    {
        var n=V("n"); var f=V("f");
        var pred=Seq(LambdaLower,Sp,f,Colon,Sp,Arrow(Product(Call("Fin",n),Fin(6)),Fin(8)),
            Sp,Mapsto,Sp,Call("Legal",f));
        return All("n",V("Nat"),Eq(Call("a",n),Call("Finset.card",Call("Finset.filter",pred,Call("Finset.univ")))));
    }

    private static Formula ClaimFormula()
    {
        var x=V("X"); var n=V("n");
        Formula A(Formula k) => Call("a",k);
        var series=Call("PowerSeries.mk",Seq(LambdaLower,Sp,n,Colon,Sp,V("Nat"),Sp,Mapsto,Sp,Par(Seq(A(n),Colon,Sp,V("Rat")))));
        var numerator=Mul(Mul(D(4),x),Add(Sub(D(5,9),Mul(D(1,0,3,0,4),x)),Mul(D(3,5,6,3,5,2),Pow(x,D(2)))));
        var denominator=Mul(Sub(D(1),Mul(D(6,4),x)),Sub(D(1),Mul(D(1,2,8),x)));
        var gf=Seq(Eq(series,Mul(numerator,Pow(denominator,new Formula.Negate(Num(1))))),Sp,Name("in"),Sp,Call("PowerSeries",V("Rat")));
        var closed=All("n",V("Nat"),Imp(Le(D(2),n),Eq(A(n),Mul(Pow(D(6,4),Sub(n,D(1))),Add(Pow(D(2),n),D(6,0))))));
        var recurrence=All("n",V("Nat"),Imp(Le(D(4),n),Eq(Seq(A(n),Colon,Sp,V("Int")),
            Sub(Mul(D(1,9,2),Seq(A(Sub(n,D(1))),Colon,Sp,V("Int"))),Mul(D(8,1,9,2),Seq(A(Sub(n,D(2))),Colon,Sp,V("Int")))))));
        return Iff(Call("claim"),And(Eq(A(D(1)),D(2,3,6)),And(gf,And(closed,recurrence))));
    }

    private static Formula RectangleFormula()
    {
        var n=V("n"); var f=V("f"); var i=V("i"); var j=V("j"); var k=V("k"); var p=V("p");
        Formula C(Formula r, Formula s) => Call("beta",App(f,Pair(r,s)));
        Formula H(Formula s) => Call("xor",C(D(0),Call("Fin.castSucc",s)),C(D(0),Call("Fin.succ",s)));
        Formula T(Formula r) => Call("xor",C(r,D(0)),C(Add(r,D(1)),D(0)));
        var reconstruction=All("i",Call("Fin",n),All("j",Fin(6),Eq(C(i,j),Call("xor",Call("xor",C(i,D(0)),C(D(0),D(0))),C(D(0),j)))));
        var horizontal=All("j",Fin(5),Ne(H(j),D(0)));
        var vertical=All("i",V("Nat"),Imp(Lt(Add(i,D(1)),n),And(Ne(T(i),D(0)),All("j",Fin(5),Ne(H(j),T(i))))));
        var exhaustive=All("k",Fin(4),Ex("p",Product(Call("Fin",n),Fin(6)),And(Le(Val(Call("Prod.fst",p)),D(1)),Eq(Call("beta",App(f,p)),k))));
        var seen=All("d",Fin(3),Ex("p",Product(Call("Fin",n),Fin(6)),And(Le(Val(Call("Prod.fst",p)),D(1)),Eq(Val(App(f,p)),Add(Val(V("d")),D(1))))));
        return All("n",V("Nat"),Imp(Le(D(2),n),All("f",Arrow(Product(Call("Fin",n),Fin(6)),Fin(8)),
            Imp(Call("Legal",f),And(reconstruction,And(horizontal,And(vertical,And(exhaustive,seen))))))));
    }

    private static Formula Iff(Formula a, Formula b) => Seq(Par(a),Sp,Longleftrightarrow,Sp,Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Rank(Formula p) => Add(Mul(D(6), Val(Call("Prod.fst", p))), Val(Call("Prod.snd", p)));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
