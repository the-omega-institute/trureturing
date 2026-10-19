using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class NathansonProblem12AffineInvarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/nathanson2026sumintersections");
    private const string Question =
        "Problem 12 (p. 21) asks verbatim: “Let (A_q) and (A′_q) be asymptotically strictly decreasing sequences of sets of integers such that A′_q = sA_q + t for all q ∈ ℕ and some s, t ∈ ℤ with s ∉ {0, ±1}. Does this imply H(A_q) = H(A′_q)?” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective affine maps preserve the sum intersection set, answering Nathanson's Problem 12 affirmatively.",
        H("Affine invariance of sum intersection sets"),
        Blocks(
            Node("AsymptoticallyStrictlyDecreasing", "Asymptotically strict decrease", DecreasingFormula(),
                "Section 2 (p. 3) states: “A sequence (A_q) of subsets of a set S is decreasing if A_q ⊇ A_{q+1} for all q ∈ ℕ … A decreasing sequence (A_q) is asymptotically strictly decreasing if A_q ≠ A_{q+1} for infinitely many q ∈ ℕ.” "
                    + "The positive-natural index type ℕ+ represents the source's ℕ = {1, 2, 3, …}. The set of indices where adjacent sets differ must be infinite.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("H", "The sum intersection set", HFormula(),
                "Section 1 (p. 1) defines “the h-fold sumset hA = {a₁ + a₂ + ⋯ + a_h : a_i ∈ A for all i = 1, …, h}”. "
                    + "It then states (p. 2): “For an additive semigroup S and index set Q, we define the sum intersection set” H(A_q) = {h ∈ ℕ : hA = ⋂_{q∈Q} hA_q}, with A = ⋂_{q∈Q} A_q. "
                    + "Here h is a Lean natural number restricted by 0 < h. SMul.smul h B denotes Mathlib's pointwise h-fold sumset, rather than the image of B under multiplication by h. Set.iInter takes the intersection over every positive-natural index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The affirmative answer", Disp(Equal(Call("claim"), Parenthesized(ClaimBody()))),
                Question + "The proposition answers this question affirmatively. Integer multiplication followed by translation is expressed by Set.image; both sequences retain the stated decrease assumptions.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Affine invariance", Disp(ClaimBody()),
                "Multiplication by s ≠ 0 followed by translation is injective. Injective images commute with intersections over the nonempty index type ℕ+. "
                    + "Distributing the h-fold sumset over the affine image changes its translation to h times t. Rewriting both sides through that image and reflecting equality by injectivity proves H A = H A′. "
                    + "The argument uses s ∉ {0, 1, −1} only to obtain s ≠ 0 and does not use either decrease premise.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nathanson-2026-problem-12-affine-invariance"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("nathanson12-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Apply(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Apply(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula AllPrimeA(Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Apos, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PNat() => new Formula.Power(Nat(), Plus);
    private static Formula Integer() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Family() => new Formula.TypeArrow(PNat(), Call("Set", Integer()));
    private static Formula SetOf(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Inter(Formula body) => Qualified("Set", "iInter", Fun("q", PNat(), body));
    private static Formula Sumset(Formula h, Formula set) => Qualified("SMul", "smul", h, set);

    private static Formula DecreasingFormula()
    {
        var a = F.Id("A");
        var q = F.Id("q");
        var next = Apply(a, Add(q, D(1)));
        var current = Apply(a, q);
        var decreasing = All("q", PNat(),
            new Formula.Relation(next, FormulaRelationOperator.SubsetOf, current));
        var different = new Formula.Relation(current, FormulaRelationOperator.NotEqual, next);
        var infinite = Qualified("Set", "Infinite", SetOf("q", PNat(), different));
        return Disp(All("A", Family(), Equal(Call("AsymptoticallyStrictlyDecreasing", a),
            Parenthesized(And(decreasing, infinite)))));
    }

    private static Formula HFormula()
    {
        var a = F.Id("A");
        var h = F.Id("h");
        var aq = Apply(a, F.Id("q"));
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, h);
        var equality = Equal(Sumset(h, Inter(aq)), Inter(Sumset(h, aq)));
        return Disp(All("A", Family(), Equal(Call("H", a), SetOf("h", Nat(), And(positive, equality)))));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var ap = Seq(F.Id("A"), Apos);
        var s = F.Id("s");
        var t = F.Id("t");
        var affine = Fun("a", Integer(), Add(Mul(s, F.Id("a")), t));
        var images = All("q", PNat(), Equal(Apply(ap, F.Id("q")),
            Qualified("Set", "image", affine, Apply(a, F.Id("q")))));
        var excluded = Seq(OpenBrace, D(0), Comma, Sp, D(1), Comma, Sp, Minus, D(1), CloseBrace);
        var multiplier = Seq(Neg, Sp, Parenthesized(new Formula.Relation(s,
            FormulaRelationOperator.MemberOf, Parenthesized(Seq(excluded, Sp, Colon, Sp, Call("Set", Integer()))))));
        var body = Equal(Call("H", a), Call("H", ap));
        body = Imp(Call("AsymptoticallyStrictlyDecreasing", a),
            Imp(Call("AsymptoticallyStrictlyDecreasing", ap), Imp(images, Imp(multiplier, body))));
        return All("A", Family(), AllPrimeA(Family(), All("s", Integer(), All("t", Integer(), body))));
    }
}
