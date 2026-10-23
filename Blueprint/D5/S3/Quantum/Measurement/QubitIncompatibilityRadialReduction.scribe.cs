using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QubitIncompatibilityRadialReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative cosines reduce incompatible volume to ordered-root coordinates.",H("Qubit Incompatibility Radial Reduction"), Blocks(
        Node("rootDensity","Ordered-root density","The density vanishes unless 1-u-U is positive. Its remaining factors are the two root differences and the two square roots.",DescribeRole.Definition,RootDensity()),
        Node("rootI","Ordered-root integral","Integrate the nonnegative part of rootDensity over two copies of rootDomain.",DescribeRole.Definition,
            Equal(X("rootI"),LIntegral("p",Q("OrderedRootCoordinates","rootDomain"),LIntegral("q",Q("OrderedRootCoordinates","rootDomain"),OfReal(Call("rootDensity",X("p"),X("q"))))))),
        Node("volume_NJM_rootI","Exact incompatible volume","Relative-cosine integration and the ordered-root Jacobian cancel the radial factors. The incompatible volume is 4π² times rootI.",DescribeRole.Theorem,
            Equal(Volume(Q("OrderedRootCoordinates","NJM")),Mul(OfReal(Mul(N(4),Pow(PiReal(),2))),X("rootI"))))
        ),[]));
    private static Formula RootDensity()
    {
        var p=X("p");var q=X("q");var u=Proj(p,1);var v=Proj(p,2);var U=Proj(q,1);var V=Proj(q,2);
        var a=Sub(Sub(N(1),u),U);var b=Sub(Sub(N(1),v),V);
        var body=Conditional(Less(N(0),a),Div(Mul(Mul(Sub(u,v),Sub(U,V)),SqrtOf(Mul(a,b))),
            Mul(App(Q("OrderedRootCoordinates","xCoord"),u,v),App(Q("OrderedRootCoordinates","xCoord"),U,V))),N(0));
        return All("p",RR(),All("q",RR(),Equal(Call("rootDensity",p,q),body)));
    }

    private static Formula X(string n) => F.Id(n);
    private static Formula N(int n) => new Formula.Number(n);
    private static Formula R() => Seq(Mathbb, Grp(X("R")));

    private static Formula RR() => Product(R(), R());
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Q(string owner, string n) => Seq(Operatorname, Grp(X(owner), Dot, X(n)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);

    private static Formula Proj(Formula a, int i) => Seq(Parenthesized(a), Dot, N(i));
    private static Formula Pow(Formula a, int n) => new Formula.Power(Parenthesized(a), N(n));
    private static Formula Mul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);

    private static Formula SqrtOf(Formula a) => App(Q("Real", "sqrt"), a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, X(n), Sp, Colon, Sp, t, Comma, Sp, b);

    private static Formula OfReal(Formula a) => App(Q("ENNReal", "ofReal"), a);
    private static Formula Volume(Formula a) => App(Q("MeasureTheory", "volume"), a);
    private static Formula PiReal() => Q("Real", "pi");

    private static Formula Conditional(Formula p, Formula a, Formula b) => Call("ite", p,a,b);
    private static Formula LIntegral(string n, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Seq(Int, Caret, Grp(Minus)),
            Seq(X(n), Colon, Sp, RR(), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body), Sp,
        X("d"), Q("MeasureTheory", "volume"));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        Formula formula, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
