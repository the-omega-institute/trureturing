using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ExponentExchange;

internal sealed class RoughPrimeRobinSuffixBellmanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Robin suffix maxima retain the accumulated integer in every denominator.",
        H("Same-integer Robin suffix maxima"),
        Blocks(
            Paragraph(Text(
                "Use q, S, W, F and Rough from RoughPrimeSuffixBellman: q(y,i) is the "
                + "i-th prime above y, S(y,i,t) is its consecutive prime-power product, "
                + "W(y,i,t) is its normalized sigma product, and F(y,i,b,h,t) means "
                + "Ordered(h,t) and S(y,i,t) <= b. All number variables are natural "
                + "numbers and t is a finite list of natural exponents. Write "
                + "L(x) = log(log(x)), with natural x cast into the reals, and "
                + "Z(n) = sigma1(n)/n. The score R(C,y,i,t) is W(y,i,t)/L(C S(y,i,t)). "
                + "T(C,y,i,b,h) denotes robinV: the semantic maximum of this score over "
                + "the finite feasible list set when b >= 1, and zero otherwise. "
                + "The maximum is noncomputable; no numerical evaluation is asserted. "
                + "The recurrence uses Lean's totalized Real.log and real division, "
                + "including division by zero equal to zero. The rough-integer bound "
                + "assumes C >= 3, so its relevant double logarithms are positive.")),
            Paragraph(Text(
                "A(C,y,i,b,h) denotes robinBranchValues. It contains the terminal "
                + "value 1/L(C), and G(q(y,i),a) T(C q(y,i)^a,y,i+1,div(b,q(y,i)^a),a) "
                + "for every natural a with 1 <= a <= h and q(y,i)^a <= b. "
                + "Here G(q,a) is the reciprocal geometric sum and div is natural "
                + "division. Thus both the accumulated integer and the remaining "
                + "budget change on a branch. Multiplicative reassociation preserves "
                + "the exact integer C S in the nonlinear denominator.")),
            Result("robin_bellman_complete", "Exact branches and attainment", BellmanFormula(),
                "For every state with positive budget, the four clauses give the "
                + "finite branch equation, the upper bound for every actual feasible "
                + "suffix, an attaining feasible suffix, and strict budget descent. "
                + "The branch identity uses the same full integer in the parent and "
                + "child score. Nonnegativity of G transports each child's attained "
                + "maximum even without a sign assumption on L."),
            Result("rough_robin_bound", "Finite rough-integer score bound", RoughFormula(),
                "The cap c(y,B) is the reused rootCap, Nat.log(q(y,0),B). "
                + "At the individual budget n, rough_prime_suffix_complete supplies "
                + "an ordered representative m <= n with W >= Z(n). Since C >= 3 "
                + "and m >= 1, L(C m) is positive and no larger than L(C n). "
                + "Dividing in the correct direction therefore bounds the score at "
                + "the original integer by that of an actual feasible suffix. "
                + "Increasing the budget and root cap places this suffix in the "
                + "finite root state, where robin_bellman_complete supplies its bound. "
                + "This theorem gives a finite comparison, not a uniform numerical "
                + "Robin threshold or a proof of RH."),
            Paragraph(Text(
                "Assume that 2,3,5,7 are coprime to the external modulus W. "
                + "For the exact 5040 valuation fibre, write N = 5040 n. "
                + "The existing jointFiber5040_mul_iff supplies n != 0 and "
                + "coprimality to W times 210. Thus n is 7-rough, and N <= B "
                + "gives n <= div(B,5040). Apply rough_robin_bound with C=5040, "
                + "y=7 and budget div(B,5040), then multiply by 403/105 using "
                + "normalized_sigma_5040_mul_of_coprime. This bounds Z(N)/L(N) "
                + "by (403/105) T(5040,7,0,div(B,5040),c(7,div(B,5040))). "
                + "The Bellman equation exposes its finite root branches. "
                + "This application drops the external W restriction; the relaxed "
                + "maximizer need not belong to that W-restricted fibre. "
                + "The fibre fixes the valuations at 2,3,5,7 exactly to 4,2,1,1. "
                + "The actual least-crossing results supply only 5040 divisibility, "
                + "so this application does not cover all least-crossing candidates.")))));

    private static DocumentBlock.Describe Result(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("robin-suffix-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula I(string name) => F.Id(name);
    private static Formula Seq(params Formula[] xs) => F.Seq([.. xs.SelectMany(x => new[] { x, F.Sp })]);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(I(name), [.. xs]);
    private static Formula Nat => F.Seq(Mathbb, Grp(I("N")));
    private static Formula Lists => Call("List", Nat);
    private static Formula All(params string[] names) => Seq(Forall, Sp,
        Seq([.. names.Select((n, i) => Seq(i == 0 ? Sp : Comma, I(n)))]), Colon, Nat, Comma);
    private static Formula ListQuant(Formula q) => Seq(q, Sp, I("t"), Colon, Lists, Comma);
    private static Formula V => Call("T", I("C"), I("y"), I("i"), I("b"), I("h"));
    private static Formula Feasible => Call("F", I("y"), I("i"), I("b"), I("h"), I("t"));
    private static Formula Score => Call("R", I("C"), I("y"), I("i"), I("t"));
    private static Formula Pow => new Formula.Power(Call("q", I("y"), I("i")), I("a"));

    private static Formula BellmanFormula() => Disp(new Formula.Aligned([
        Seq(All("C", "y", "i", "b", "h"), D(1), Le, I("b"), Rightarrow, OpenBracket),
        Seq(V, Eq, Call("max", Call("A", I("C"), I("y"), I("i"), I("b"), I("h")))),
        Seq(Land, Open, ListQuant(Forall), Feasible, Rightarrow, Score, Le, V, Close),
        Seq(Land, Open, ListQuant(Exists), Feasible, Land, Score, Eq, V, Close),
        Seq(Land, Open, All("a"), D(1), Le, I("a"), Land, Pow, Le, I("b"),
            Rightarrow, Call("div", I("b"), Pow), Lt, I("b"), Close, CloseBracket)
    ]));

    private static Formula RoughFormula() => Disp(Seq(All("C", "y", "B", "n"),
        D(3), Le, I("C"), Land, D(1), Le, I("y"), Land, D(1), Le, I("n"), Le, I("B"),
        Land, Call("Rough", I("y"), I("n")), Rightarrow,
        new Formula.Fraction(Call("Z", I("n")), Call("L", Seq(I("C"), Cdot, I("n")))), Le,
        Call("T", I("C"), I("y"), D(0), I("B"), Call("c", I("y"), I("B")))));
}
