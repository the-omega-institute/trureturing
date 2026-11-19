using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticLargeEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every size at least eleven, exactly two translated integer patterns maximize the plastic-template count and minimize the corresponding real-power sumset.",
        H("Equality patterns from eleven points onward"),
        Blocks(
            Paragraph(Text("Let E be any finite subset of the integers, and put n=|E|. Write C(E) for the total number of translates contained in E of "
                + "{0,2,3,4}, {0,3,5,6}, {0,5,7}, and {0,5,8,9}. All intervals below contain integers. "
                + "For a natural number n, define S₀(n)=[0,n−1] and S₁(n)={0}∪[2,n], with integer endpoints. "
                + "Write translate(a,S)={a+z : z ∈ S} and A(r,E)={rᶻ : z ∈ E}. "
                + "The sum A(r,E)+A(r,E) is the actual finite real sumset. Negative exponents, negative translations, and unbounded gaps are allowed. "
                + "The statement below assumes n≥11; the ten-point case has two additional patterns.")),
            Describe.Lean(DescribeId.Create("plastic-large-complete-equality"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticLargeEquality.whole_large_equality"),
                H("The two equality shapes"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("Remove the largest element y from an actual exponent set, and let x be the largest remaining element. "
                    + "The exact insertion identity expresses the change in C as the number of templates completed at y, which is at most four. "
                    + "Together with the preceding prefix bound, equality forces both equality for that prefix and an increment of four. "
                    + "All four templates are completed precisely when y−1, y−2, y−3, y−4, y−6, y−7, and y−9 belong to the prefix. "
                    + "In particular, y−1 belongs to it, so maximality gives y=x+1. "
                    + "At ten points the four possible translated patterns are already known. The pattern {0,1}∪[3,10] cannot extend with increment four: "
                    + "its next point would be 11, but the required point 2 is absent. Similarly, {0,3}∪[5,12] would have to extend by 13 while the required point 4 is absent. "
                    + "The interval and single-gap patterns do extend: adding their maximum plus one supplies all seven required points and preserves the same form. "
                    + "Induction on the actual finite set therefore proves both directions of the classification for every larger size. "
                    + "For r>1 satisfying r³=r+1, the collision identity gives |A(r,E)+A(r,E)|+C(E)=n(n+1)/2. "
                    + "Since n≥11 implies n(n+1)/2≥4n, the natural-number subtraction in the displayed sumset value agrees with ordinary integer subtraction. "
                    + "Thus the same two shapes are exactly the sets attaining n(n+1)/2−4n+26."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula P(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string x, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..a]);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Card(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Implies,P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.And,P(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Or,P(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Iff,P(b));
    private static Formula Statement()
    {
        var e=V("E"); var n=Card(e); var a=V("a"); var r=V("r");
        var integers=Seq(Mathbb,Grp(V("Z"))); var reals=Seq(Mathbb,Grp(V("R")));
        Formula Shape(byte j) => Eq(e,Call("translate",a,
            new Formula.Apply(new Formula.Subscript(V("S"),D(j)),[n])));
        var classified=Ex("a",integers,Or(Shape(0),Shape(1)));
        var countCase=IffF(Eq(Call("C",e),Sub(Mul(D(4),n),D(2,6))),classified);
        var powers=Call("A",r,e);
        var triangular=new Formula.Fraction(Mul(n,P(Add(n,D(1)))),D(2));
        var extremum=Add(Sub(triangular,Mul(D(4),n)),D(2,6));
        var sumCase=IffF(Eq(Card(Add(powers,powers)),extremum),classified);
        var realCase=All("r",reals,Imp(Rel(D(1),FormulaRelationOperator.LessThan,r),
            Imp(Eq(new Formula.Power(r,D(3)),Add(r,D(1))),sumCase)));
        return Disp(All("E",Call("Finset",integers),
            Imp(Rel(D(1,1),FormulaRelationOperator.LessThanOrEqual,n),And(countCase,realCase))));
    }
}
