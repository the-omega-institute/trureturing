using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticExtremalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp minimum of a sumset inside the integer powers of a plastic root, with the least uniform size threshold ten.",
        H("Sharp plastic-power sumsets from lossless finite memory"),
        Blocks(
            Paragraph(Text("Fix r > 1 with r³ = r + 1. For a finite integer set E, write A(r,E) = {rᵉ : e ∈ E}. "
                + "C(E) counts all translates contained in E of T₄={0,2,3,4}, T₆={0,3,5,6}, T₇={0,5,7}, and T₉={0,5,8,9}. "
                + "N_d(E) is the number of integer starting points t with t+T_d contained in E. "
                + "M(n) = n(n+1)/2, L(n) = M(n)−4n+26, and I(a,n) = [a,a+n−1] over the integers. "
                + "The Lean count is proved equal to the four literal filters in the frozen collision theorem, "
                + "via the bijection from each starting exponent to its unique right endpoint. "
                + "Natural n ≥ 10 covers exactly the original integer size range. Exponents and the translation a may be negative; "
                + "no bound on the diameter, gap lengths or product set is imposed. "
                + "MinimumSumsetInPowerGroup(r,n) means the least element of the set of |A+A| for finite real A "
                + "with A contained in {rᶻ : z an integer} and |A|=n. "
                + "LeastUniformCopyCountThreshold means the least integer N such that for every finite integer E, "
                + "N ≤ |E| implies C(E) ≤ 4|E|−26, with the latter inequality interpreted in the integers.")),
            Describe.Lean(DescribeId.Create("plastic-extremal-template-count"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticExtremal.count"),
                H("Four literal translated templates"),
                StatementSource.FromAuthor(Disp(All("E",Call("Finset",Seq(Mathbb,Grp(V("Z")))),
                    Eq(Call("C",V("E")),Add(Add(Add(Call("N",D(4),V("E")),
                        Call("N",D(6),V("E"))),Call("N",D(7),V("E"))),Call("N",D(9),V("E"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("Lean counts the unique right endpoints of these copies. "
                    + "The source-count bridge translates each starting point by its template span, "
                    + "proving equality with the four original filters before using the frozen sumset identity."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("plastic-sharp-extremal-threshold-ten"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticExtremal.whole_theorem_three_one"),
                H("Theorem 3.1: sharp extremum and smallest uniform threshold"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("Insert the exponent points in increasing order. The current state records exactly those distances "
                    + "0 through 8 occupied behind the current maximum. The four rewards are evaluated in the full shifted state "
                    + "before truncation, so a required distance of 9 is counted correctly. A gap at least 9 resets the state and has reward zero. "
                    + "Actual prefix induction carries both the table bound and the fact that its potential entry is non-sentinel (less than 15): the sentinel 15 "
                    + "never serves as a legitimate bound. Every allowed transition of the source's ten-layer table is checked by Lean's kernel. "
                    + "This is an upper-bound certificate, not a claim that the table computes exact optima. "
                    + "It gives at most 14 copies on ten points; each later actual maximum creates at most four copies. "
                    + "Every translated interval has counts n−4, n−6, n−7 and n−9, attaining the bound. "
                    + "The frozen plastic collision identity transfers the result to actual real sumsets. "
                    + "The Bérczes reference attests the collision classification, not the finite-memory extremal theorem proved here. "
                    + "For any finite A inside the full group r^ℤ, the injective power map supplies an equal-cardinality finite exponent preimage. "
                    + "Thus the minimum is taken over all such A, not just consecutive powers. "
                    + "The actual nine-point set {0} ∪ [2,9] has eleven copies, excluding every integer threshold below ten. "
                    + "This does not classify all equality cases or prove the later stability and deletion theorems."))),
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
        var r=V("r"); var n=V("n"); var e=V("E"); var a=V("a");
        var ae=Call("A",r,e); var interval=Call("I",a,n); var ai=Call("A",r,interval);
        var cmax=Sub(Mul(D(4),n),D(2,6)); var l=Call("L",n);
        var universal=All("E",Call("Finset",Seq(Mathbb,Grp(V("Z")))),
            Imp(Eq(Card(e),n),And(Le(Call("C",e),cmax),Le(l,Card(Add(ae,ae))))));
        var attained=All("a",Seq(Mathbb,Grp(V("Z"))),
            And(Eq(Card(interval),n),And(Eq(Call("C",interval),cmax),Eq(Card(Add(ai,ai)),l))));
        var minimum=Eq(Call("MinimumSumsetInPowerGroup",r,n),l);
        var threshold=Eq(Call("LeastUniformCopyCountThreshold"),D(1,0));
        var body=And(universal,And(attained,And(minimum,threshold)));
        body=All("n",Seq(Mathbb,Grp(V("N"))),Imp(Le(D(1,0),n),body));
        body=Imp(Rel(D(1),FormulaRelationOperator.LessThan,r),
            Imp(Eq(new Formula.Power(r,D(3)),Add(r,D(1))),body));
        return Disp(All("r",Seq(Mathbb,Grp(V("R"))),body));
    }
}
