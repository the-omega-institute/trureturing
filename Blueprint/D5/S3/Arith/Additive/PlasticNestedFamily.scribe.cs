using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticNestedFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original plastic nested-family theorem, with exact sumset and product counts and comparison to the actual golden-ratio powers.",
        H("The original nested plastic family"),
        Blocks(
            Paragraph(Text("Fix a real r > 1 with r³ = r + 1. Let E(n) = {0,3} ∪ [5,n+2] over the integers, "
                + "B(r,n) = {rᵉ : e ∈ E(n)}, φ = (1+√5)/2, and G(n) = {φᵉ : 0 ≤ e ≤ n−1, e an integer}. "
                + "All sets in the formula are actual finite subsets of the reals. The same B(r,n) supplies every clause. "
                + "The next exponent set is {0,3} ∪ [5,n+3], exactly E(n+1). Natural indices n ≥ 7 parametrize every original integer index n ≥ 7. "
                + "Write M(n) = n(n+1)/2 and C(n) = n−1+(n−8)₊+(n−9)₊+(n−11)₊+1[n≥8]+1[n≥10]. "
                + "The symbol (x)₊ means max(x,0); Lean's natural subtractions implement these positive parts. "
                + "Write S(r) = {r⁰,r³,r⁵,r⁶,r⁷,r⁸,r⁹}.")),
            Describe.Lean(DescribeId.Create("plastic-original-whole-theorem-two-one"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticNestedFamily.whole_theorem_two_one"),
                H("Theorem 2.1: all scales in the same family"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("The exponent map is strictly increasing, so E(n) has n distinct images and its new endpoint proves strict nesting. "
                    + "The actual exponent sumset is {0,3} ∪ [5,2n+4], giving the exact product cardinality 2n+2. "
                    + "The collision module gives the exact actual sumset count, including all boundary terms. "
                    + "For the golden-ratio comparison, normalization of an equal sum gives only (d,a,b)=(3,2,2). "
                    + "The sum map is therefore injective on the sorted pairs excluding outer gap three. There are M(n)−(n−3) such pairs, "
                    + "so |G(n)+G(n)| ≥ M(n)−(n−3). Since C(n) ≥ n−1, the claimed separation by two follows. "
                    + "The seven-point member is identified by its exact exponent set, using the same r. "
                    + "This identification does not reprove the existing frozen seven-point refutation. "
                    + "The real-root assumptions are retained; root existence is already supplied by plastic_root in SumProductGoldenMinimizerRefutation."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula P(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string x, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..a]);
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Card(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Implies,P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.And,P(b));
    private static Formula Statement()
    {
        var r = V("r"); var n = V("n");
        var b = Call("B",r,n); var g = Call("G",n); var m = Call("M",n); var c = Call("C",n);
        var prod = Card(Mul(b,b)); var sum = Card(Add(b,b));
        var clauses = new Formula[] {
            Rel(b,FormulaRelationOperator.SubsetOf,Call("B",r,Add(n,D(1)))),
            Eq(Card(b),n), Eq(prod,Add(Mul(D(2),n),D(2))), Le(prod,Sub(Mul(D(3),n),D(4))),
            Eq(sum,Sub(m,c)), Le(sum,Sub(Card(Add(g,g)),D(2))),
            Imp(Eq(n,D(7)),Eq(b,Call("S",r))) };
        var body = clauses.Aggregate(And);
        var strictNesting = Seq(b,Sp,Subset,Sp,Call("B",r,Add(n,D(1))));
        body = And(strictNesting,clauses.Skip(1).Aggregate(And));
        body = All("n",Seq(Mathbb,Grp(V("N"))),Imp(Le(D(7),n),body));
        body = Imp(Rel(D(1),FormulaRelationOperator.LessThan,r),
            Imp(Eq(new Formula.Power(r,D(3)),Add(r,D(1))),body));
        return Disp(All("r",Seq(Mathbb,Grp(V("R"))),body));
    }
}
