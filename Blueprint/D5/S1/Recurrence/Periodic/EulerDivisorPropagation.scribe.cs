using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerDivisorPropagationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerDivisorPropagation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary A000111 satisfies both complete A386381 Conjecture 2 assertions.", H("A386381 Conjecture 2 for ordinary Euler numbers"), Blocks(
            Paragraph(Text("Corrected Euler coefficients propagate zeros at every positive odd-prime-power index.")),
            Paragraph(Text("Write q=p raised to r+1, and epsilon=(-1) raised to b times floor(p/2). All parameters are natural; b is zero or one. Residue arithmetic is in ZMod q. The deleted frequencies form an exact finite bijection. The correction factor is a unit at every positive index, including indices smaller than r+1. This reconstructs a consequence of Young's prior Kummer congruence, without a p-adic premise.")),
            Node("corrected_sum", "The prime-deleted frequency identity", Q("p r b j",Imp(Call("Prime",V("p")),Imp(Call("Odd",V("p")),Imp(LeN(V("b"),D(1)),Eqn(Mul(Sub(D(1),Mul(Pow(R(Qmod(),MinusOne()),Mul(V("b"),Call("div",V("p"),D(2)))),Pow(R(Qmod(),V("p")),V("j")))),R(Qmod(),A(V("b"),V("j")))),FilteredSum()))))),
                "Subtract the p-scaled shorter odd-length sum from the full sum. The divisible frequencies have h=p*v+b*floor(p/2).", DescribeRole.Theorem),
            Node("signed_zero_transfer", "Every positive signed zero transfers", Q("p r b k m",Imp(Call("Prime",V("p")),Imp(Call("Odd",V("p")),Imp(LeN(V("b"),D(1)),Imp(LtN(D(0),V("k")),Imp(Eqn(R(Qmod(),A(V("b"),V("k"))),D(0)),Eqn(R(Qmod(),A(V("b"),Shift(V("k"),V("m"),Qmod()))),D(0)))))))),
                "Every retained frequency is a unit. Euler periodicity equates their powers, and nilpotence of p proves the correction factor invertible.", DescribeRole.Theorem),
            Paragraph(Text("E denotes the source-normalized ordinary A000111 carrier with E(0)=1. Every parameter below is natural, and phi is Nat.totient. Odd prime powers use corrected zero transfer; the two-primary component uses the tangent bound; prime-power divisibility assembles them in the same E value.")),
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
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role,
        openProblemResolutionClaim: name == "divisor_propagation"
            ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a386381-ordinary-euler-totient-propagation"),
                ResolutionKind.Proved,
                [DeclarationHandle.Create(Prefix + "particular")])
            : null);

    private static Formula V(string n) => F.Id(n);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(P(x), Sp, Implies, Sp, P(y));
    private static Formula Dvd(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula LtN(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Q(string names, Formula body)
    {
        foreach (var n in names.Split(' ').Reverse()) body = All(n, Nat(), body);
        return body;
    }
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..args]);
    private static Formula E(Formula n) => Call("E",n);
    private static Formula Phi(Formula n) => Call("totient",n);
    private static Formula Shift(Formula k, Formula m, Formula d) => Add(k,Mul(m,Phi(d)));


    private static Formula Qmod() => Pow(V("p"),Add(V("r"),D(1)));

    private static Formula LeN(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula A(Formula b, Formula n) => Call("A",b,n);
    private static Formula R(Formula q, Formula x) => Call("residue",q,x);
    private static Formula MinusOne() => P(Seq(Minus, D(1)));
    private static Formula FilteredSum() => Seq(
        new Formula.Subscript(F.Sum, Seq(V("h"), Sp, InMacro, Sp,
            Call("filter",Call("range",Qmod()),
                Seq(V("h"), Sp, Mapsto, Sp, Neg, Sp, P(Dvd(V("p"),Add(Mul(D(2),V("h")),V("b")))))))),
        Sp, P(Mul(Pow(R(Qmod(),MinusOne()),V("h")),Pow(R(Qmod(),Add(Mul(D(2),V("h")),V("b"))),V("j")))));

}
