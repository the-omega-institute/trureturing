using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerDivisorPropagationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerDivisorPropagation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "E denotes the source-normalized ordinary A000111 carrier with E(0)=1. Every parameter below is natural, and phi is Nat.totient. The result is an unfrozen Stage A candidate pending independent pre-freeze review; neither source exposition nor generated prose establishes publication or a resolution KPI. Odd prime powers use corrected zero transfer; the two-primary component uses the tangent bound; prime-power divisibility assembles them in the same E value.", H("A386381 Conjecture 2 for ordinary Euler numbers"), Blocks(
            Paragraph(Text("E denotes the source-normalized ordinary A000111 carrier with E(0)=1. Every parameter below is natural, and phi is Nat.totient. The result is an unfrozen Stage A candidate pending independent pre-freeze review; neither source exposition nor generated prose establishes publication or a resolution KPI. Odd prime powers use corrected zero transfer; the two-primary component uses the tangent bound; prime-power divisibility assembles them in the same E value.")),
            Node("odd_prime_power", "The ordinary all-positive-index local theorem", Q("p r k m",Imp(Call("Prime",V("p")),Imp(Call("Odd",V("p")),Imp(LtN(D(0),V("k")),Imp(Dvd(Qmod(),E(V("k"))),Dvd(Qmod(),E(Shift(V("k"),V("m"),Qmod())))))))),
                "The totient is even, so both indices use the same signed branch. Each sign is a unit and therefore preserves zero divisibility.", DescribeRole.Theorem),
            Node("divisor_propagation", "The complete main assertion", Q("k m d",Imp(LtN(D(2),V("d")),Imp(Dvd(V("d"),E(V("k"))),Dvd(V("d"),E(Shift(V("k"),V("m"),V("d"))))))),
                "This is the entire main source assertion, including m=0, every early index, every composite modulus and both prime-power branches. There is no eventual-period, spectrum or positivity premise.", DescribeRole.Theorem),
            Node("particular", "The complete particular family", Q("k m",Imp(Seq(V("k"), Sp, Neq, Sp, D(3)),Dvd(E(V("k")),E(Shift(V("k"),V("m"),E(V("k"))))))),
                "Indices zero, one and two have divisor one. For k at least four the proved bound E(k)>2 allows the main assertion. Only k=3 is excluded, exactly as in the source.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula f, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("eulerdivisorpropagation-" + name.Replace('_','-').ToLowerInvariant()),
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


    private static Formula Qmod() => Pow(V("p"),Add(V("r"),D(1)));

}
