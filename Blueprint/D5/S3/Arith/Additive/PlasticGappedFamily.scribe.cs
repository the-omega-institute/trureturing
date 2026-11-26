using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticGappedFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing exponent one gives an exact nonconsecutive family and a strict nine-point sumset comparison.",
        H("A gapped family of plastic powers"),
        Blocks(
            Paragraph(Text("Let F(n) = {0} ∪ [2,n] over the integers, where an interval with upper endpoint below its lower endpoint is empty. "
                + "For a real r, let A(r,n) = {rᵉ : e ∈ F(n)} and P(r) = {rᵉ : 0 ≤ e ≤ 8, e an integer}. "
                + "For a finite integer set E, C(E) denotes the sum of the four literal translation counts: "
                + "starting points t in E for which {t+2,t+3,t+4}, {t+3,t+5,t+6}, {t+5,t+7}, "
                + "or {t+5,t+8,t+9}, respectively, lie in E. This is the same count used in the plastic collision identity. "
                + "Write L(n) = n(n+1)/2−4n+26. Every real-power assertion retains r > 1 and r³ = r + 1. "
                + "Natural n ≥ 10 parametrizes the full integer range in question.")),
            Describe.Lean(DescribeId.Create("plastic-gapped-exponent-family"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticGappedFamily.family"),
                H("The exponent family"), StatementSource.FromAuthor(Disp(
                    All("n",Nat(),Eq(Call("F",V("n")),Call("Union",Call("Singleton",D(0)),Call("IccZ",D(2),V("n"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Union and Singleton have their usual set meanings, and IccZ is the closed integer interval. "
                    + "The integer one is deliberately absent, but both zero and two are present once n is at least two."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("plastic-gapped-whole-proposition"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticGappedFamily.whole_proposition_five_one"),
                H("Exact counts and the nine-point obstruction"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("For n ≥ 10, the four starting-point sets in F(n) are exactly "
                    + "{0} ∪ [2,n−4], {0} ∪ [2,n−6], {0} ∪ [2,n−7], and {0} ∪ [2,n−9]. "
                    + "Their cardinalities are n−4, n−6, n−7, and n−9, even at the empty-interval boundary n=10. "
                    + "The existing plastic collision identity then gives the actual sumset formula. Strict increase of rᵉ "
                    + "ensures that the power images have the stated cardinality. "
                    + "For n=9 the four counts are 5,3,2,1, whereas the consecutive exponent set [0,8] has counts 5,3,2,0. "
                    + "Subtracting these counts from the 45 unordered pairs gives 34 and 35 distinct sums. "
                    + "The absent interior exponent witnesses that F(n) is not an integer interval. "
                    + "This result establishes the explicit family and its exact counts; it does not classify every equality case "
                    + "or independently establish a global minimum over arbitrary exponent sets. "
                    + "The cited Bérczes work supports the reused collision mechanism, not a priority claim for this gapped-family result."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula P(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string x, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..a]);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Nat() => Seq(Mathbb,Grp(V("N")));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Card(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Implies,P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.And,P(b));
    private static Formula Member(Formula a, Formula b) => Rel(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Root(Formula r, Formula b) => All("r",Seq(Mathbb,Grp(V("R"))),
        Imp(Rel(D(1),FormulaRelationOperator.LessThan,r),Imp(Eq(new Formula.Power(r,D(3)),Add(r,D(1))),b)));
    private static Formula Statement()
    {
        var n=V("n"); var r=V("r"); var e=Call("F",n); var a=Call("A",r,n);
        var structural=And(Eq(Card(e),n),And(Member(D(0),e),And(new Formula.Not(Member(D(1),e)),Member(D(2),e))));
        var counts=Eq(Call("C",e),Sub(Mul(D(4),n),D(2,6)));
        var real=Root(r,And(Eq(Card(a),n),Eq(Card(Add(a,a)),Call("L",n))));
        var large=All("n",Nat(),Imp(Le(D(1,0),n),And(structural,And(counts,real))));
        var nine=Call("A",r,D(9)); var p=Call("P",r);
        var small=Root(r,And(Eq(Card(nine),D(9)),And(Eq(Card(p),D(9)),
            And(Eq(Card(Add(nine,nine)),D(3,4)),And(Eq(Card(Add(p,p)),D(3,5)),
                Rel(Card(Add(nine,nine)),FormulaRelationOperator.LessThan,Card(Add(p,p))))))));
        return Disp(And(large,small));
    }
}
