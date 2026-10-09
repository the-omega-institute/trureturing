using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FourVectorSignSumBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FourVectorSignSumBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FourVectorSignSumBound: exact analytic statements for four-qubit white-noise compatibility.",
        H("FourVectorSignSumBound"),
        Blocks(
            Node("signedSum", "signedSum", "A sign tuple assigns a coefficient +1 or −1 to each of the four vectors.", DescribeRole.Definition, AssessedProvenance.FromRepo(), Ambient(All("x", Arrow(Fin(4), X("E")), All("e", Signs(), Equal(Call("signedSum", X("x"), X("e")), SumOver("i", Fin(4), Smul(Call("sgn", Apply(X("e"), X("i"))), Apply(X("x"), X("i"))))))))),
            Node("maxNorm", "maxNorm", "The maximum ranges over all sixteen sign tuples.", DescribeRole.Definition, AssessedProvenance.FromRepo(), Ambient(All("x", Arrow(Fin(4), X("E")), Equal(Call("maxNorm", X("x")), Apply(Seq(Qualified("Finset", "sup"), Apos), Qualified("Finset", "univ"), LambdaOf("e", Signs(), Norm(Call("signedSum", X("x"), X("e"))))))))),
            Node("signedSum_le_max", "signedSum_le_max", "Each signed sum is bounded by the finite maximum.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), Ambient(All("x", Arrow(Fin(4), X("E")), All("e", Signs(), LE(Norm(Call("signedSum", X("x"), X("e"))), Call("maxNorm", X("x"))))))),
            Node("four_vector_inequality", "four_vector_inequality", "Singular Gram positivity and a triangle decomposition of the four-sign constraints yield the universal bound. Zero columns are handled separately. The coefficient is attained by three planar trine vectors of length three and a perpendicular vector of length four.", DescribeRole.Theorem, AssessedProvenance.FromRepo(), All("x", Arrow(Fin(4), Vectors()), LE(SumOver("i", Fin(4), Norm(Apply(X("x"), X("i")))), Multiply(Fraction(Root(Num(13)), Num(2)), Call("maxNorm", X("x"))))))), []));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role, AssessedProvenance provenance, Formula formula) => Describe.Lean(
        DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula BoolType() => X("Bool");
    private static Formula Vectors() => Call("EuclideanSpace", Reals(), Fin(3));
    private static Formula Signs() => Arrow(Fin(4), BoolType());
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula LambdaOf(string v, Formula type, Formula body) => Seq(X("fun"), Sp, Typed(X(v),type), Sp, Mapsto, Sp, body);
    private static Formula Ambient(Formula body) => All("E", X("Type"), Seq(OpenBracket, Call("NormedAddCommGroup", X("E")), CloseBracket, Comma, Sp, OpenBracket, Call("InnerProductSpace", Reals(), X("E")), CloseBracket, Comma, Sp, body));
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Root(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula SumOver(string v, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(X(v),t)), Sp, b);
}
