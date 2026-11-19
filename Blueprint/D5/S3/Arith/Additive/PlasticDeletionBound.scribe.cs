using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticDeletionBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "After any h deletions leaving n consecutive-interval plastic powers with n at least eight and 11h + 24 at most 3n, their sumset is smaller than the golden-power sumset.",
        H("Arbitrary deletions from a plastic-power interval"),
        Blocks(
            Paragraph(Text("Fix r > 1 with r³ = r + 1. For natural numbers n,h and an integer a, let I(a,n,h) = [a,a+n+h−1] be an integer interval. "
                + "For any H contained in I(a,n,h) with |H| = h, put E = I(a,n,h) ∖ H and A(r,a,n,h,H) = {rᵉ : e ∈ E}. "
                + "Let φ = (1+√5)/2, G(n) = {φᵉ : e an integer, 0 ≤ e ≤ n−1}, and M(n) = n(n+1)/2. "
                + "All sums and products below are those of actual finite sets of real numbers. "
                + "The conditions n ≥ 8 and 11h+24 ≤ 3n express exactly the integer range 0 ≤ h ≤ floor((3n−24)/11). "
                + "Natural-number subtraction in the conclusion agrees with integer subtraction throughout this range.")),
            Describe.Lean(DescribeId.Create("plastic-arbitrary-deletion-four-one"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticDeletionBound.whole_theorem_four_one"),
                H("No restriction on the deleted positions"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("For a finite offset template T containing zero, each missing point destroys at most |T| translated copies. "
                    + "Indeed every destroyed start has the form x−u for a deleted point x and an offset u in T. "
                    + "The four plastic collision templates have spans 4,6,7,9 and cardinalities 4,4,3,4. In an interval of length m their surviving counts are at least "
                    + "(m−4)₊−4h, (m−6)₊−4h, (m−7)₊−3h, and (m−9)₊−4h, respectively. "
                    + "Summing yields C(E)+26+15h ≥ 4m, also at m=8 where the last template has no copies. "
                    + "With m=n+h, the collision identity |A+A|+C(E)=M(n) gives the stated numerical sumset bound. "
                    + "The golden-power lower bound |G(n)+G(n)| ≥ M(n)−(n−3), together with 11h+24 ≤ 3n, gives the final separation by one. "
                    + "Strict monotonicity of integer powers gives |A|=n. Every product exponent lies in [2a,2a+2(n+h)−2], "
                    + "which gives the product bound, and the same hypothesis implies 2(n+h)−1 ≤ 3n−4."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula P(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string x, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..a]);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
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
        var r=V("r"); var n=V("n"); var h=V("h"); var a=V("a"); var holes=V("H");
        var A=Call("A",r,a,n,h,holes); var G=Call("G",n);
        var product=Sub(Mul(D(2),P(Add(n,h))),D(1));
        var bound=Add(Add(Sub(Call("M",n),Mul(D(4),n)),D(2,6)),Mul(D(1,1),h));
        var body=new Formula[] { Eq(Card(A),n), Le(Card(Mul(A,A)),product),
            Le(product,Sub(Mul(D(3),n),D(4))), Le(Card(Add(A,A)),bound),
            Le(bound,Sub(Card(Add(G,G)),D(1))) }.Aggregate(And);
        body=Imp(Eq(Card(holes),h),body);
        body=Imp(Rel(holes,FormulaRelationOperator.SubsetOf,Call("I",a,n,h)),body);
        body=All("H",Call("Finset",Seq(Mathbb,Grp(V("Z")))),body);
        body=All("a",Seq(Mathbb,Grp(V("Z"))),body);
        body=Imp(Le(Add(Mul(D(1,1),h),D(2,4)),Mul(D(3),n)),body);
        body=Imp(Le(D(8),n),body);
        body=All("h",Seq(Mathbb,Grp(V("N"))),body);
        body=All("n",Seq(Mathbb,Grp(V("N"))),body);
        body=Imp(Eq(new Formula.Power(r,D(3)),Add(r,D(1))),body);
        body=Imp(Rel(D(1),FormulaRelationOperator.LessThan,r),body);
        return Disp(All("r",Seq(Mathbb,Grp(V("R"))),body));
    }
}
