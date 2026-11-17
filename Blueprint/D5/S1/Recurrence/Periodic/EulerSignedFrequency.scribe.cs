using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerSignedFrequencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerSignedFrequency.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All indices and exponents are natural numbers. A is integer-valued; F and exp are rational formal power series. C embeds constants. The residue function casts an integer or natural value to ZMod of its first argument. All arithmetic inside a residue identity is in that ring. Young supplies the prior ordinary congruence component; the finite derivation here proves the integral identities directly.", H("Integral Euler frequency identities"), Blocks(
            Paragraph(Text("All indices and exponents are natural numbers. A is integer-valued; F and exp are rational formal power series. C embeds constants. The residue function casts an integer or natural value to ZMod of its first argument. All arithmetic inside a residue identity is in that ring. Young supplies the prior ordinary congruence component; the finite derivation here proves the integral identities directly.")),
            Node("A", "Integral derivatives", Q("b", And(Eqn(A(V("b"),D(0)),D(1)), Q("n", Eqn(A(V("b"),Add(V("n"),D(1))),Sub(Pow(V("b"),Add(V("n"),D(1))),Sum("i",Add(V("n"),D(1)),Mul(Mul(Call("choose",Add(V("n"),D(1)),V("i")),Pow(D(2),Sub(V("n"),V("i")))),A(V("b"),V("i"))))))))),
                "The integer recurrence constructs every derivative before modular reduction. Natural binomial coefficients and b are cast to the integers.", DescribeRole.Definition),
            Node("F", "The signed exponential series", Q("b", Eqn(B(V("b")),InfiniteSum("n",Div(Mul(A(V("b"),V("n")),Pow(V("X"),V("n"))),Call("factorial",V("n")))))),
                "X is the distinguished formal indeterminate. The integer coefficients A are embedded in the rationals; no factorial is inverted in a residue ring.", DescribeRole.Definition),
            Node("generating_identity", "The exact exponential identity", Q("b",Eqn(Mul(Add(D(1),Pow(Exp(),D(2))),B(V("b"))),Mul(C(D(2)),Pow(Exp(),V("b"))))),
                "Factorial-normalized coefficient comparison reduces the identity to the integral recurrence.", DescribeRole.Theorem),
            Node("finite_identity", "The finite odd-length identity", Q("b L",Imp(Call("Odd",V("L")),Eqn(Mul(Add(D(1),Pow(Exp(),Mul(D(2),V("L")))),B(V("b"))),Mul(C(D(2)),Sum("h",V("L"),Mul(C(Pow(MinusOne(),V("h"))),Pow(Exp(),Add(Mul(D(2),V("h")),V("b"))))))))),
                "The alternating geometric sum has numerator one plus the Lth power exactly when L is odd.", DescribeRole.Theorem),
            Node("branch_equations", "The signed branch equations", And(Eqn(Der(B(D(0))),Mul(B(D(0)),Sub(B(D(0)),D(2)))),And(Eqn(Der(B(D(1))),Mul(B(D(1)),Sub(B(D(0)),D(1)))),Eqn(Pow(B(D(1)),D(2)),Mul(B(D(0)),Sub(D(2),B(D(0))))))),
                "Differentiation and cancellation of the nonzero exponential denominator prove both differential equations and the quadratic relation.", DescribeRole.Theorem),
            Node("scaled_moment", "Integral finite moments modulo an odd modulus", Q("b L u q j",Imp(Call("Odd",V("L")),Imp(Call("Odd",V("q")),Imp(Dvd(V("q"),Mul(V("u"),V("L"))),Eqn(Mul(Pow(R(V("q"),V("u")),V("j")),R(V("q"),A(V("b"),V("j")))),Sum("h",V("L"),Mul(Pow(R(V("q"),MinusOne()),V("h")),Pow(R(V("q"),Mul(V("u"),Add(Mul(D(2),V("h")),V("b")))),V("j"))))))))),
                "Positive-order exponential derivatives contain the modulus. The remaining factor two is cancelled using oddness of q. This includes j=0.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula f, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("eulersignedfrequency-" + name.Replace('_','-').ToLowerInvariant()),
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
