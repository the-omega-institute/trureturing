using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerSecantBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerSecantBridge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "a is the existing integer A000364 carrier in SecantNumberPurePeriodRefutation. E is ordinary A000111. The exponential identity gives the inverse hyperbolic cosine convolution; its even coefficients, combined with the exact ordinary sign bridge, satisfy the original secant recurrence. The existing a_unique theorem identifies the carriers.", H("Reusing the existing secant carrier"), Blocks(
            Paragraph(Text("a is the existing integer A000364 carrier in SecantNumberPurePeriodRefutation. E is ordinary A000111. The exponential identity gives the inverse hyperbolic cosine convolution; its even coefficients, combined with the exact ordinary sign bridge, satisfy the original secant recurrence. The existing a_unique theorem identifies the carriers.")),
            Node("secant_bridge", "Exact A000364 correspondence", Q("s",Eqn(E(Mul(D(2),V("s"))),Call("a",V("s")))),
                "Equality is in the integers, with the natural E value cast. No independent secant carrier is introduced.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula f, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("eulersecantbridge-" + name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(f)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string n) => F.Id(n);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula And(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Imp(Formula x, Formula y) => Seq(P(x), Sp, Implies, Sp, P(y));
    private static Formula Dvd(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula LtN(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula LeN(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Negate(Formula x) => Seq(Minus, P(x));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Q(string names, Formula body)
    {
        foreach (var n in names.Split(' ').Reverse()) body = All(n, Nat(), body);
        return body;
    }
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..args]);
    private static Formula Sum(string n, Formula bound, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(n), Sp, InMacro, Sp, Call("range",bound))), Sp, P(body));
    private static Formula InfiniteSum(string n, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(n), Sp, InMacro, Sp, Nat())), Sp, P(body));
    private static Formula E(Formula n) => Call("E",n);
    private static Formula A(Formula b, Formula n) => Call("A",b,n);
    private static Formula B(Formula b) => Call("F",b);
    private static Formula Der(Formula f) => Call("derivative",f);
    private static Formula Co(Formula f) => Call("constantCoeff",f);
    private static Formula Exp() => Call("exp",Rat());
    private static Formula C(Formula x) => Call("C",x);
    private static Formula Phi(Formula n) => Call("totient",n);
    private static Formula R(Formula q, Formula x) => Call("residue",q,x);
    private static Formula MinusOne() => Negate(D(1));
    private static Formula Shift(Formula k, Formula m, Formula d) => Add(k,Mul(m,Phi(d)));


}
