using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ExponentExchange;

internal sealed class RoughPrimeSuffixBellmanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact rough-integer maximum is attained by a consecutive prime suffix.",
        H("Rough Prime Suffix Maxima"),
        Blocks(
            Paragraph(Text(
                "Write q(y,i) for the i-th prime strictly above y, S(y,i,t) for the "
                + "product of its consecutive prime powers with exponent list t, and "
                + "W(y,i,t) for the product of reciprocal geometric sums G(q,a). "
                + "Both empty products are one. F(y,i,b,h,t) means that t has positive, "
                + "weakly decreasing entries, its first entry is at most h, and S is at "
                + "most b. R(y,n) means every prime divisor of n is greater than y. "
                + "Z(n) is sigma1(n)/n in the real numbers. V is the semantic maximum "
                + "of W over F, U is the maximum of Z over rough integers in [1,B], "
                + "and c(y,B) is the natural logarithm of B to base q(y,0).")),
            Result("feasible_finite", "Finite suffix states", FiniteFormula(),
                "For arbitrary natural y, i, b and h, the feasible list set is finite. "
                + "The represented positive integer exceeds the list length, and every "
                + "entry is at most h. Thus only finitely many lists can fit the state."),
            Result("bellman_complete", "Complete branches and attained upper bounds",
                BellmanFormula(),
                "Here J(y,i,b,h) consists of one and every G(q(y,i),a) times "
                + "V(y,i+1,div(b,q(y,i)^a),a), for 1 <= a <= h and q(y,i)^a <= b. "
                + "The operation div is natural division. The four displayed clauses "
                + "are denoted C(y,i,b,h) below. Splitting a nonempty exponent list "
                + "gives exactly one legal branch; joining a legal head to a child "
                + "suffix gives a feasible parent. Positive branches strictly reduce "
                + "the integer budget, so every branch path terminates. No positive "
                + "branch is omitted, and a zero head ends the entire suffix."),
            Result("rough_maximizer_order", "Ordered valuations at a rough maximum",
                MaximizerFormula(),
                "The valuation v(n,p) is Nat.factorization n evaluated at p. "
                + "The finite rough-integer family contains one and has a maximizing "
                + "member. An inversion of allowed prime valuations, including a zero "
                + "valuation at the smaller prime, gives a smaller rough integer with "
                + "strictly greater Z by prime exponent exchange."),
            Result("suffix_prime_factors", "Actual suffix prime support", SupportFormula(),
                "Every prime divisor of S occurs at a position of the actual exponent "
                + "list. Distinct positions use strictly increasing primes. In "
                + "particular S is positive and rough, even when the list is empty."),
            Result("rough_prime_suffix_complete", "Equality with the global rough maximum",
                CompleteFormula(),
                "For every y >= 1 and B >= 1, all six displayed clauses hold. C retains "
                + "the complete branch equation, every suffix upper bound, attainment, "
                + "and strict budget descent for every state with b >= 1. The prime "
                + "sequence contains every prime above y, and a <= c is equivalent "
                + "to the first prime power fitting B. The sigma identity holds for "
                + "every suffix list, without an ordering assumption. The existential "
                + "clause gives one actual rough maximizing integer and a feasible "
                + "suffix representing that exact integer. Its weight is U, and U "
                + "equals the root suffix maximum. This includes B = 1, c = 0 and "
                + "the empty suffix. No executable evaluator or certificate checker "
                + "is defined by these semantic maxima."),
            Paragraph(Text(
                "To reconstruct a maximizing integer, enumerate its prime valuations "
                + "over a finite range bounded by primeCounting(n). The valuation "
                + "order makes the positive entries an initial consecutive prefix: "
                + "once a valuation is zero, all later entries are zero. Factorization "
                + "reconstruction recovers n exactly. Coprimality of a head prime "
                + "with the tail and the prime-power sigma formula identify W with Z. "
                + "The full first prime power divides n, giving the logarithmic head "
                + "bound. This suffix gives U <= V; an attaining feasible suffix "
                + "gives a positive rough integer in [1,B], proving V <= U.")))));

    private static DocumentBlock.Describe Result(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rough-suffix-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula I(string name) => F.Id(name);
    private static Formula S => Call("S", I("y"), I("i"), I("t"));
    private static Formula W => Call("W", I("y"), I("i"), I("t"));
    private static Formula V => Call("V", I("y"), I("i"), I("b"), I("h"));
    private static Formula Q => Call("q", I("y"), I("i"));
    private static Formula Cap => Call("c", I("y"), I("B"));
    private static Formula Root => Call("V", I("y"), D(0), I("B"), Cap);
    private static Formula U => Call("U", I("y"), I("B"));
    private static Formula Feasible => Call("F", I("y"), I("i"), I("b"), I("h"), I("t"));
    private static Formula Power(Formula x, Formula a) => new Formula.Power(x, a);
    private static Formula All(params string[] names) => Seq(Forall, Sp,
        Seq([.. names.Select((name, index) => Seq(index == 0 ? Sp : Comma, I(name)))]), Comma, Sp);
    private static Formula Some(params string[] names) => Seq(Exists, Sp,
        Seq([.. names.Select((name, index) => Seq(index == 0 ? Sp : Comma, I(name)))]), Comma, Sp);

    private static Formula FiniteFormula() => Disp(Seq(All("y", "i", "b", "h"),
        Call("Finite", Seq(OpenBrace, I("t"), Mid, Feasible, CloseBrace))));

    private static Formula BellmanFormula() => Disp(new Formula.Aligned([
        Seq(All("y", "i", "b", "h"), D(1), Le, I("b"), Rightarrow),
        Seq(V, Eq, Call("max", Call("J", I("y"), I("i"), I("b"), I("h")))),
        Seq(Land, Open, All("t"), Feasible, Rightarrow, W, Le, V, Close),
        Seq(Land, Open, Some("t"), Feasible, Land, W, Eq, V, Close),
        Seq(Land, Open, All("a"), D(1), Le, I("a"), Land, Power(Q, I("a")), Le, I("b"),
            Rightarrow, Call("div", I("b"), Power(Q, I("a"))), Lt, I("b"), Close)
    ]));

    private static Formula MaximizerFormula() => Disp(new Formula.Aligned([
        Seq(All("y", "B"), D(1), Le, I("B"), Rightarrow, Some("n")),
        Seq(D(1), Le, I("n"), Le, I("B"), Land, Call("R", I("y"), I("n")),
            Land, Call("Z", I("n")), Eq, U),
        Seq(Land, Open, All("p", "q"), Call("Prime", I("p")), Land, Call("Prime", I("q")),
            Land, I("y"), Lt, I("p"), Lt, I("q"), Rightarrow,
            Call("v", I("n"), I("q")), Le, Call("v", I("n"), I("p")), Close)
    ]));

    private static Formula SupportFormula() => Disp(new Formula.Aligned([
        Seq(All("y", "i", "t"), D(0), Lt, S),
        Seq(Land, Open, All("p"), Call("Prime", I("p")), Land, Call("dvd", I("p"), S),
            Rightarrow, Some("j"), I("j"), Lt, Call("length", I("t")), Land,
            I("p"), Eq, Call("q", I("y"), Seq(I("i"), Plus, I("j"))), Close),
        Seq(Land, Call("R", I("y"), S))
    ]));

    private static Formula CompleteFormula() => Disp(new Formula.Aligned([
        Seq(All("y", "B"), D(1), Le, I("y"), Land, D(1), Le, I("B"), Rightarrow),
        Seq(Open, All("i", "b", "h"), D(1), Le, I("b"), Rightarrow,
            Call("C", I("y"), I("i"), I("b"), I("h")), Close),
        Seq(Land, Open, All("p"), Open, Call("Prime", I("p")), Land, I("y"), Lt, I("p"),
            Close, Leftrightarrow, Some("i"), I("p"), Eq, Q, Close),
        Seq(Land, Open, All("a"), I("a"), Le, Cap, Leftrightarrow,
            Power(Call("q", I("y"), D(0)), I("a")), Le, I("B"), Close),
        Seq(Land, Open, All("i", "t"), Call("Z", S), Eq, W, Close),
        Seq(Land, Open, Some("n", "t"), D(1), Le, I("n"), Le, I("B"), Land,
            Call("R", I("y"), I("n")), Land, Call("F", I("y"), D(0), I("B"), Cap, I("t"))),
        Seq(Land, Call("S", I("y"), D(0), I("t")), Eq, I("n"), Land,
            Call("W", I("y"), D(0), I("t")), Eq, U, Close),
        Seq(Land, U, Eq, Root)
    ]));
}
