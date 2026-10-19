using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class MartinezMirrorGamblersRuinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/martinez2024mirrorgamblersruin");

    private const string Conjecture =
        "Conjecture 5.1 (page 16): “Consider the generalization of the gambler’s ruin problem when we add a mirror step. "
        + "If the particle starts at x = 1, then lim_{N→∞} f_N^{(p)}(1) = "
        + "[√((p + 1)(1 − 3p + 4p²)) − (1 − 2p)(p + 1)] / [2p(p + 1)] "
        + "whenever we restrict the particle moves by either moving from x to x − 1 with probability q₁, "
        + "or from x to x + 1 with probability p, or from x to N − x with probability q₂ "
        + "where q₁ = q₂ = (1 − p)/2.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mirror-step ruin probability has Martinez's conjectured limit.",
        H("Martinez's mirror-step gambler's ruin limit"),
        Blocks(
            Node("IsWinProbability", "The boundary recurrence",
                All("p", R, All("N", Nat, All("f", Arrow(Nat, R),
                    Equal(Call("IsWinProbability", X("p"), X("N"), X("f")),
                        Parenthesized(RecurrenceBody()))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Section 4.1 (page 11) states: “Define f(x)=f_N^{(p)}(x) as the probability that a particle starting at x "
                + "will eventually reach N.” The boundary values are f(0)=0 and f(N)=1. "
                + "Conjecture 5.1 (page 16) specifies: “whenever we restrict the particle moves by either moving from x to x − 1 "
                + "with probability q₁, or from x to x + 1 with probability p, or from x to N − x with probability q₂ "
                + "where q₁ = q₂ = (1 − p)/2.” Thus the right-step probability is p and both the left and mirror probabilities "
                + "are (1 − p)/2. N and x are natural numbers; subtraction of natural indices is truncated. "
                + "The equation adds transition weights when two destinations coincide. Values beyond N are unrestricted."),
            Node("limitValue", "The conjectured radical",
                All("p", R, Equal(Call("limitValue", X("p")), LimitValueBody())),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), Conjecture),
            Node("claim", "Conjecture 5.1 as a limit statement",
                Equal(X("claim"), Parenthesized(ClaimBody())),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Conjecture + " The parameter p ranges over all real numbers strictly between zero and one. "
                + "The family f assigns a real-valued function on the natural numbers to every N. "
                + "For every N at least two its restriction to zero through N satisfies IsWinProbability. "
                + "The conclusion is convergence of f N 1 along the natural-number filter atTop."),
            Node("result", "Proof of the complete limit conjecture", ClaimBody(),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "For positive left, right and mirror weights a,b,c with a+b+c=1, put T=(a+b)/(ab)−2 and "
                + "r=(T−√(T²−4))/2. Then 0<r<1. Set K₁=1−a/r−br, K₂=1−ar−b/r and R=K₁/c. "
                + "The identity K₁K₂=c² and the inequality K₁+K₂<0 give R<0. "
                + "The two coefficient equations are 1=a/r+br+cR and R=aRr+bR/r+c. "
                + "They verify the finite formula (1−rˣ)(1−Rr^{N − x})/((1−R)(1−rᴺ)). "
                + "The numerator is a constant plus a linear combination of rˣ and r^{N − x}, "
                + "so the coefficient equations give the recurrence, and the two endpoint values are zero and one."),
            Paragraph(Text(
                "Uniqueness requires only a>0 and b,c≥0. The difference of two solutions has zero boundary values. "
                + "Choose a maximum on the finite interval. At an interior maximizer the averaging equation and "
                + "the positive left weight force the left neighbour to attain the same maximum. "
                + "Strong induction reaches a boundary and makes the maximum zero. Applying the argument "
                + "to both differences proves equality throughout the interval.")),
            Paragraph(Text(
                "At x=1 the powers rᴺ and r^{N−1} tend to zero, giving the limit (1−r)/(1−R). "
                + "For a=c=(1 − p)/2 and b=p this positive limit L satisfies "
                + "p(p + 1)L²+(1 − 2p)(p + 1)L−p(1−p)=0. The positive square-root branch gives limitValue p. "
                + "Equality of the finite solutions for every N≥2 transfers convergence to every family in claim. "
                + "The expected duration of the walk is a separate question.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("martinez-mirror-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);

    private static Formula RecurrenceBody()
    {
        Formula p = X("p"), n = X("N"), x = X("x");
        Formula left = Mul(Div(Subtract(D(1), p), D(2)), Call("f", Subtract(x, D(1))));
        Formula right = Mul(p, Call("f", Add(x, D(1))));
        Formula mirror = Mul(Div(Subtract(D(1), p), D(2)), Call("f", Subtract(n, x)));
        return And(Equal(Call("f", D(0)), D(0)),
            And(Equal(Call("f", n), D(1)), All("x", Nat,
                Imp(Lt(D(0), x), Imp(Lt(x, n), Equal(Call("f", x), Add(Add(left, right), mirror)))))));
    }

    private static Formula LimitValueBody()
    {
        Formula p = X("p"), plus = Parenthesized(Add(p, D(1)));
        Formula radicand = Mul(plus, Parenthesized(Add(Subtract(D(1), Mul(D(3), p)), Mul(D(4), Pow(p, D(2))))));
        Formula correction = Mul(Parenthesized(Subtract(D(1), Mul(D(2), p))), plus);
        return Div(Subtract(App(Qualified("Real", "sqrt"), radicand), correction), Mul(Mul(D(2), p), plus));
    }

    private static Formula ClaimBody()
    {
        Formula p = X("p"), n = X("N");
        Formula hypothesis = All("N", Nat, Imp(Le(D(2), n),
            Call("IsWinProbability", p, n, Call("f", n))));
        Formula sequence = Parenthesized(Seq(n, Colon, Nat, Sp, Mapsto, Sp, Call("f", n, D(1))));
        Formula limit = App(Qualified("Filter", "Tendsto"), sequence,
            Qualified("Filter", "atTop"), Call("nhds", Call("limitValue", p)));
        return All("p", R, Imp(Lt(D(0), p), Imp(Lt(p, D(1)),
            All("f", Arrow(Nat, Arrow(Nat, R)), Imp(hypothesis, limit)))));
    }
}
