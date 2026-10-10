using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class BiquadraticKroneckerTimesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/BiquadraticKroneckerTimes.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two independent nonsquare classes over the rationals force four-coefficient independence of real quadratic roots; an integer-character condition gives approximation sequences on every finite torus.",
        H("Biquadratic independence and integer approximation times"), Blocks(
            Node("biquadratic_independent", "Four rational coefficients vanish", IndependenceFormula(),
                "Assume x squared is p, y squared is q, x is irrational, and neither q nor pq is a rational square. Squaring the relation and separating the rational and x coefficients gives two equations. Their product eliminates the coefficient of xy through the nonsquare obstructions. The remaining coefficients then vanish. All rational coefficients and radicands are explicitly cast to the reals where necessary.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("dense_circle_sequence", "Every torus target is approached", SequenceFormula(),
                "The character criterion TorusOrbitClosure.result identifies the closure of nonnegative powers. The assumption says that any integer combination of the frequencies which is an integer has all coefficients zero; equivalently the frequencies together with one have no nontrivial integer relation. The sequential characterization of closure then supplies natural exponents tending to the prescribed target. The exponents need not be monotone or unbounded, and no algebraicity assumption is imposed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("bmp-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula All(string v, Formula ty, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), ty, body);
    private static Formula Some(string v, Formula ty, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), ty, body);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula App(Formula x, params Formula[] args) => new Formula.Apply(x, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        App(Qualified(owner, name), args);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula x, Formula ty) => Parenthesized(Seq(x, Colon, ty));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Inst(string cls, Formula ty) => Seq(OpenBracket, Call(cls, ty), CloseBracket, Sp);
    private static Formula Lambda(string v, Formula ty, Formula body) =>
        Parenthesized(Seq(F.Id(v), Colon, ty, Sp, Mapsto, Sp, body));
    private static Formula Limit(Formula f, Formula z) =>
        Call("Tendsto", f, F.Id("atTop"), Call("nhds", z));

    private static Formula IndependenceFormula()
    {
        Formula p=F.Id("p"), q=F.Id("q"), x=F.Id("x"), y=F.Id("y");
        Formula assumptions=And(Equal(Pow(x,D(2)),Cast(p,R)),
            And(Equal(Pow(y,D(2)),Cast(q,R)), And(Call("Irrational",x),
                And(new Formula.Not(Call("IsSquare",q)), new Formula.Not(Call("IsSquare",Mul(p,q)))))));
        Formula relation=Equal(Add(Add(Add(Cast(F.Id("a"),R), Mul(Cast(F.Id("b"),R),x)),
            Mul(Cast(F.Id("c"),R),y)), Mul(Cast(F.Id("d"),R), Parenthesized(Mul(x,y)))),D(0));
        Formula vanish=And(Equal(F.Id("a"),D(0)),And(Equal(F.Id("b"),D(0)),
            And(Equal(F.Id("c"),D(0)),Equal(F.Id("d"),D(0)))));
        return Disp(All("p",Q,All("q",Q,All("x",R,All("y",R,Implies(assumptions,
            All("a",Q,All("b",Q,All("c",Q,All("d",Q,Implies(relation,vanish)))))))))));
    }
    private static Formula SequenceFormula()
    {
        Formula i=F.Id("I"), a=F.Id("a"), z=F.Id("z"), j=F.Id("i");
        Formula sum=Seq(new Formula.Subscript(Sum,new Formula.Relation(j,FormulaRelationOperator.MemberOf,i)),Sp,
            Mul(Cast(Call("k",j),R),Call("a",j)));
        Formula independence=All("k",Arrow(i,Z),All("m",Z,
            Implies(Equal(sum,Cast(F.Id("m"),R)),All("i",i,Equal(Call("k",j),D(0))))));
        Formula powers=Lambda("n",N,Lambda("i",i,Pow(QCall("Circle","exp",
            Mul(Mul(D(2),Qualified("Real","pi")),Call("a",j))),Call("m",F.Id("n")))));
        return Disp(All("I",F.Id("Type"),Seq(Inst("Fintype",i),All("a",Arrow(i,R),
            Implies(independence,All("z",Arrow(i,F.Id("Circle")),
                Some("m",Arrow(N,N),Limit(powers,z))))))));
    }
}
