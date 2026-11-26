using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticTailStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The deficit in the plastic-template count controls missing endpoint patterns, large gaps, and actual consecutive intervals in the tail.",
        H("Right-endpoint defects and consecutive tails"),
        Blocks(
            Paragraph(Text("All exponent sets are finite subsets of the integers. Write C(E) for the count of the four plastic templates, represented by their unique right endpoints. "
                + "The indicator ind(Q) is 1 when Q holds and 0 otherwise. The integer interval I(a,b) is {t ∈ Z : a ≤ t ≤ b}. "
                + "For x : N → Z, P(x,k) consists of x(0),…,x(k−1). The values of x outside the first n positions are unrestricted. "
                + "Strict increase is required only for 0 ≤ i < j < n, so every increasingly enumerated finite integer set is included, without any restriction on signs or gap sizes.")),
            Describe.Lean(DescribeId.Create("plastic-completed-endpoint-patterns"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticTailStability.completed"),
                H("Completed patterns at an endpoint"), StatementSource.FromAuthor(CompletedStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("Each summand tests the earlier points required by one of the four right-endpoint offset sets {1,2,4}, {1,3,6}, {2,7}, and {1,4,9}. "
                    + "Only membership of these predecessors is tested; the endpoint itself need not belong to E in this definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("plastic-integer-prefix-set"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticTailStability.prefixSet"),
                H("The finite prefix set"), StatementSource.FromAuthor(PrefixStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("Here range(k) is {0,…,k−1} and image(x,S) is the finite image {x(i) : i ∈ S}. "
                    + "Under strict increase on the first n positions, this prefix has cardinality k whenever k ≤ n."))), DescribeRole.Definition),
            Paragraph(Text("For the theorem, set E=P(x,n), P=P(x,10), T=E∖P, c(i)=completed(P(x,i),x(i)), δ=4n−26−C(E), and K=1+floor(δ/3). "
                + "Define B={i ∈ N : 10 ≤ i < n and c(i)<4}, B₂={i ∈ N : 10 ≤ i < n and x(i)−x(i−1)=2}, "
                + "and B₃={i ∈ N : 10 ≤ i < n and x(i)−x(i−1)≥3}. "
                + "Union(R) denotes the union of the finite family R, and tailImage(x,m,n)={x(i) : m ≤ i < n}. "
                + "The zero-based indices 10,…,n−1 are precisely the endpoints after the first ten points; index 9 is the tenth point. "
                + "The count bound makes δ the ordinary nonnegative integer deficit. Likewise C(P) ≤ 14 and every c(i) ≤ 4, so the subtractions in the deficit identity are not truncated. "
                + "Since K is positive, floor((n−10+K−1)/K) equals ceil((n−10)/K).")),
            Describe.Lean(DescribeId.Create("plastic-right-endpoint-tail-stability"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticTailStability.whole_theorem_three_three"),
                H("Defect accounting and tail stability"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("Every completed template has one right endpoint, so C(E) is the sum of its endpoint contributions. "
                    + "Positive offsets ensure that the contribution at x(i) is already determined by its preceding prefix. Splitting this sum after ten points gives the exact defect identity. "
                    + "The ten-point bound gives C(P) ≤ 14; each incomplete endpoint contributes at least one unit of deficit. "
                    + "A gap of two excludes all three patterns requiring offset one, and a gap of at least three excludes every pattern, since each requires offset one or two. "
                    + "Their losses are therefore at least three and four, respectively. "
                    + "The starts of consecutive runs in T are its least point and some of the gap endpoints. Thus their number is at most 1+|B₂|+|B₃| ≤ K. "
                    + "Taking the longest interval among these runs and bounding the cardinality of their union proves the rounded-up length bound. "
                    + "If δ ≤ 2, no gap after the tenth point can exceed one, so all points from x(9) through x(n−1) fill their integer interval. "
                    + "When n=10 this last interval is a singleton; the separate nonempty-tail conclusion is asserted only when n>10."))), DescribeRole.Theorem)),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Nat() => Seq(Mathbb,Grp(V("N")));
    private static Formula Int() => Seq(Mathbb,Grp(V("Z")));
    private static Formula Fin(Formula t) => Call("Finset",t);
    private static Formula Call(string x, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..a]);
    private static Formula App(Formula f, Formula a) => new Formula.Apply(f,[a]);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall,Sp,Par(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists,Sp,Par(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula Mem(Formula a, Formula b) => Rel(a,FormulaRelationOperator.MemberOf,b);
    private static Formula SubsetOf(Formula a, Formula b) => Rel(a,FormulaRelationOperator.SubsetOf,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Card(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula FloorDiv(Formula a, Formula b) => Seq(Lfloor,new Formula.Fraction(a,b),Rfloor);
    private static Formula CompletedStatement()
    {
        var e=V("E"); var t=V("t");
        Formula Test(params int[] offsets) => Call("ind", offsets.Select(d => Mem(Sub(t,D(checked((byte)d))),e)).Aggregate(And));
        var rhs=new[] { Test(1,2,4),Test(1,3,6),Test(2,7),Test(1,4,9) }.Aggregate(Add);
        return Disp(All("E",Fin(Int()),All("t",Int(),Eq(Call("completed",e,t),rhs))));
    }
    private static Formula PrefixStatement() => Disp(All("x",new Formula.TypeArrow(Nat(),Int()),
        All("k",Nat(),Eq(Call("P",V("x"),V("k")),Call("image",V("x"),Call("range",V("k")))))));
    private static Formula Statement()
    {
        var n=V("n"); var x=V("x"); var e=V("E"); var p=V("P"); var t=V("T"); var delta=DeltaLower; var k=V("K");
        var i=V("i"); var j=V("j"); var a=V("a"); var b=V("b"); var r=V("R"); var J=V("J");
        var interval=Call("I",a,b);
        var sum=Seq(new Formula.Subscript(Sum,And(Le(D(1,0),i),Lt(i,n))),Sp,Par(Sub(D(4),App(V("c"),i))));
        var intervalMember=Ex("a",Int(),Ex("b",Int(),And(Le(a,b),Eq(J,interval))));
        var cover=Ex("R",Fin(Fin(Int())),And(Eq(Call("Union",r),t),And(Le(Card(r),k),
            All("J",Fin(Int()),Imp(Mem(J,r),intervalMember)))));
        var longRun=Ex("a",Int(),Ex("b",Int(),And(SubsetOf(interval,t),And(Le(a,b),
            Le(FloorDiv(Sub(Add(Sub(n,D(1,0)),k),D(1)),k),Card(interval))))));
        var clauses=new Formula[] {
            Le(Call("C",e),Sub(Mul(D(4),n),D(2,6))),
            Eq(delta,Add(Sub(D(1,4),Call("C",p)),sum)),
            Le(Card(V("B")),delta),
            Le(Add(Mul(D(3),Card(new Formula.Subscript(V("B"),D(2)))),Mul(D(4),Card(new Formula.Subscript(V("B"),D(3))))),delta),
            Imp(Lt(D(1,0),n),And(cover,longRun)),
            Imp(Le(delta,D(2)),Eq(Call("tailImage",x,D(9),n),Call("I",App(x,D(9)),App(x,Sub(n,D(1)))))) };
        var mono=All("i",Nat(),All("j",Nat(),Imp(And(Lt(i,j),Lt(j,n)),Lt(App(x,i),App(x,j)))));
        return Disp(All("n",Nat(),Imp(Le(D(1,0),n),All("x",new Formula.TypeArrow(Nat(),Int()),Imp(mono,clauses.Aggregate(And))))));
    }
}
