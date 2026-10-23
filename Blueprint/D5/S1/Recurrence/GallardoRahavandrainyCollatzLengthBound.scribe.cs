using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GallardoRahavandrainyCollatzLengthBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/gallardo2025collatzlength");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero binary polynomial has Collatz length at most two plus the floor of one quarter of its squared degree.",
        H("A Quadratic Bound for Binary-Polynomial Collatz Length"),
        Blocks(
            Paragraph(Text("Polynomials have coefficients in ZMod 2. The operations M, oddPart and oddSeq "
                + "are those of GallardoRahavandrainyBinaryCollatz: M=X²+X+1, oddPart removes the "
                + "linear factors, and oddSeq A k is the source term A₂ₖ₊₁. Natural subtraction "
                + "is truncated at zero, and Nat.div denotes integer floor division. The natural "
                + "infimum sInf selects the least terminal-pair index; the proof constructs such an index.")),
            Node("evenTerm", "The even-indexed terms", EvenTermFormula(),
                "\"A₀ = A\" and \"A₂ₖ = 1 + M₁A₂ₖ₋₁\" (§1, p. 4). "
                + "The natural index k selects A₂ₖ. The displayed ite has value A when k=0 "
                + "and value 1+M*oddSeq A (k-1) otherwise.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("rA", "The source length", LengthFormula(),
                "\"Let A be a nonzero binary polynomial. Then the sequences of polynomials obtained "
                + "from Collatz transformations are of finite length r_A.\" "
                + "\"where m ∈ ℕ* and r_A = m + 1 ≤ 2^{deg(A)−1}.\" (Theorem 1.2, p. 4.) "
                + "Here m is the least positive index from which the even and odd terms are "
                + "respectively X*(X+1) and 1. This counts the terminal pair after the first odd 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The polynomial-bound prediction", Disp(Equivalent(F.Id("claim"), ClaimBody())),
                "\"However, several computations suggest that here also r_A is bounded by a "
                + "polynomial in deg(A) (see Section 3).\" (§1, p. 5.) "
                + "The polynomial p has natural coefficients, A ranges over all nonzero polynomials "
                + "over ZMod 2, and natDegree equals the degree on that domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rA_quadratic", "The explicit quadratic estimate", Disp(QuadraticBody()),
                "For an odd polynomial F different from 1, set k to the smaller multiplicity "
                + "of the roots 0 and 1 in F+1. Coprimality of X and X+1 gives k≤natDegree(F)/2. "
                + "If a Collatz step preserves the degree, both removed multiplicities equal one, "
                + "and the smaller multiplicity in F+1 decreases by one. Strong induction "
                + "therefore forces a strict degree decrease within k steps. A second strong "
                + "induction on degree, using the identity (n+1)/2+n²/4=(n+1)²/4 for natural "
                + "division, bounds the time to reach 1. The terminal pair starts at the next index. "
                + "This proves an upper bound on plateau duration; an exact duration and sharpness "
                + "of the bound are separate questions.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("result", "Proof of the polynomial-bound prediction", Disp(ClaimBody()),
                "The quadratic estimate implies the prediction with the natural-coefficient "
                + "polynomial X²+2, since floor(n²/4)≤n². The stronger explicit floor estimate "
                + "is the preceding theorem.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("grlength-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Polynomials() => Call("Polynomial", Call("ZMod", D(2)));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NeqZero(Formula value) => Seq(value, Sp, Neq, Sp, D(0));
    private static Formula Degree(Formula value) => App(Q("Polynomial", "natDegree"), value);
    private static Formula P() => Multiply(Q("Polynomial", "X"), Parenthesized(Add(Q("Polynomial", "X"), D(1))));

    private static Formula EvenTermFormula()
    {
        var a = F.Id("A");
        var k = F.Id("k");
        var next = Add(D(1), Multiply(F.Id("M"), Call("oddSeq", a, Subtract(k, D(1)))));
        return Disp(All("A", Polynomials(), All("k", Naturals(), Equal(Call("evenTerm", a, k),
            Call("ite", Equal(k, D(0)), a, next)))));
    }

    private static Formula LengthFormula()
    {
        var a = F.Id("A");
        var m = F.Id("m");
        var k = F.Id("k");
        var terminal = And(Equal(Call("evenTerm", a, k), P()), Equal(Call("oddSeq", a, k), D(1)));
        var tail = All("k", Naturals(), Imp(Leq(m, k), terminal));
        var set = Seq(OpenBrace, Typed(m, Naturals()), Sp, Bar, Sp, And(Leq(D(1), m), tail), CloseBrace);
        return Disp(All("A", Polynomials(), Equal(Call("rA", a), Add(Call("sInf", set), D(1)))));
    }

    private static Formula ClaimBody()
    {
        var p = F.Id("p");
        var a = F.Id("A");
        var evaluated = App(Q("Polynomial", "eval"), Degree(a), p);
        return Seq(Exists, Sp, Typed(p, Call("Polynomial", Naturals())), Comma, Sp,
            All("A", Polynomials(), Imp(NeqZero(a), Leq(Call("rA", a), evaluated))));
    }

    private static Formula QuadraticBody()
    {
        var a = F.Id("A");
        var budget = App(Q("Nat", "div"), new Formula.Power(Parenthesized(Degree(a)), D(2)), D(4));
        return All("A", Polynomials(), Imp(NeqZero(a), Leq(Call("rA", a), Add(D(2), budget))));
    }
}
