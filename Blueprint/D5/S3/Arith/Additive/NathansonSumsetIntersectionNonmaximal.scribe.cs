using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class NathansonSumsetIntersectionNonmaximalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/nathanson2025sumsetintersection");
    private const string Question =
        "Problem 2 (arXiv:2512.23574v3, p. 6) asks: “Let A be a subset of the infinite abelian semigroup S such that A is a nonbasis of order h but not a maximal nonbasis of order h for S. Does there exist an asymptotically strictly decreasing sequence (A_q)_{q=1}^∞ of subsets of S such that A = ⋂_{q=1}^∞ A_q and hA = ⋂_{q=1}^∞ hA_q? In particular, consider this problem for S = ℤ.” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing 2 from the even integers gives a negative answer to Nathanson's Problem 2.",
        H("A nonmaximal nonbasis obstructing sumset intersections"),
        Blocks(
            Node("sumset", "Finite sumsets", SumsetFormula(),
                "Section 1 (p. 1) states: “For every positive integer h, the h-fold sumset of A is the set of all sums of h not necessarily distinct elements of A, that is, hA = {a₁ + ⋯ + a_h : aᵢ ∈ A for all i = 1, …, h}.” The recursion uses pointwise set addition. The auxiliary value at h = 0 is the empty set; only positive orders occur in the question.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsBasis", "Bases of a fixed order", BasisFormula(),
                "Section 1 (p. 1) states: “The subset A is a basis of order h for S if hA = S, or, equivalently, if rA,h(x) ≥ 1 for all x ∈ S.” The ambient semigroup is represented by its universal set, and nonbasis means the negation of this equality.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("AsymptoticallyStrictlyDecreasing", "Asymptotically strict decrease", DecreasingFormula(),
                "Section 1 (p. 1) states: “The sequence of sets (A_q)_{q=1}^∞ is decreasing if A_q ⊇ A_{q+1} for all q ∈ ℕ.” It continues: “The decreasing sequence (A_q)_{q=1}^∞ is strictly decreasing if A_q ≠ A_{q+1} for all q ∈ ℕ and asymptotically strictly decreasing if A_q ≠ A_{q+1} for infinitely many q.” The Lean sequence starts at 0; infinitely many unequal steps are expressed by an unequal step beyond every natural bound.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal assertion in Problem 2", Disp(Equal(Call("claim"), Parenthesized(ClaimBody()))),
                Question + "Section 2 (p. 5) states: “A subset A of S is a maximal nonbasis of order h for S if A is not a basis of order h for S but every proper superset of A is a basis of order h for S.” This condition is inlined in the assertion; the private proof uses Mathlib Maximal through Set.maximal_iff_forall_ssuperset. S ranges over infinite additive commutative semigroups, h over natural numbers with 1 ≤ h, and A over all subsets. Both intersections range over every nonnegative integer q. The sumset equality is written with the intersection on the left.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A negative answer", Disp(Not(ClaimBody())),
                "Take S = ℤ, h = 2 and A = {n : ℤ | Even n ∧ n ≠ 2}. This is a nonbasis, and its proper superset of all even integers remains a nonbasis. In a decreasing family with this intersection and arbitrarily late unequal steps, every stage has infinitely many elements outside A. Removing the possible element 2 leaves infinitely many odd elements. For an odd integer n, choose such an odd element b different from n − 2; then n − b belongs to A and n = (n − b) + b belongs to the two-fold sumset of that stage. Thus 1 belongs to every stage's two-fold sumset and does not belong to A + A. This single instance refutes the universal assertion; no assertion about all finite punctures or all orders h ≥ 2 is needed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("nathanson2512-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Apply(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Set(Formula carrier) => Call("Set", carrier);
    private static Formula Family(Formula carrier) => new Formula.TypeArrow(Nat(), Set(carrier));
    private static Formula Semigroup(Formula body) =>
        All("S", Named("Type"), Instance("AddCommSemigroup", F.Id("S"), body));
    private static Formula Inter(Formula familyBody) => Qualified("Set", "iInter",
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Nat())), Sp, Mapsto, Sp, familyBody));

    private static Formula SumsetFormula()
    {
        var a = F.Id("A");
        var h = F.Id("h");
        var zero = Equal(Call("sumset", a, D(0)), Emptyset);
        var one = Equal(Call("sumset", a, D(1)), a);
        var step = All("h", Nat(), Equal(Call("sumset", a, Add(h, D(2))),
            Add(Call("sumset", a, Add(h, D(1))), a)));
        return Disp(Semigroup(All("A", Set(F.Id("S")), And(zero, And(one, step)))));
    }

    private static Formula BasisFormula()
    {
        var h = F.Id("h");
        var a = F.Id("A");
        var body = Equal(Call("sumset", a, h), Qualified("Set", "univ"));
        return Disp(Semigroup(All("h", Nat(), All("A", Set(F.Id("S")),
            Equal(Call("IsBasis", h, a), Parenthesized(body))))));
    }

    private static Formula DecreasingFormula()
    {
        var a = F.Id("A");
        var q = F.Id("q");
        var next = Apply(a, Add(q, D(1)));
        var current = Apply(a, q);
        var decreasing = All("q", Nat(),
            new Formula.Relation(next, FormulaRelationOperator.SubsetOf, current));
        var strict = All("N", Nat(), Some("q", Nat(), And(
            new Formula.Relation(F.Id("N"), FormulaRelationOperator.LessThanOrEqual, q),
            new Formula.Relation(current, FormulaRelationOperator.NotEqual, next))));
        return Disp(All("S", Named("Type"), All("A", Family(F.Id("S")),
            Equal(Call("AsymptoticallyStrictlyDecreasing", a), Parenthesized(And(decreasing, strict))))));
    }

    private static Formula ClaimBody()
    {
        var s = F.Id("S");
        var h = F.Id("h");
        var a = F.Id("A");
        var aq = F.Id("Aq");
        var stage = Apply(aq, F.Id("q"));
        var sequence = Some("Aq", Family(s), And(Call("AsymptoticallyStrictlyDecreasing", aq),
            And(Equal(Inter(stage), a), Equal(Inter(Call("sumset", stage, h)), Call("sumset", a, h)))));
        var body = Imp(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, h),
            Imp(Not(Call("IsBasis", h, a)), Imp(Not(And(Not(Call("IsBasis", h, a)),
                All("B", Set(s), Imp(Seq(a, Sp, Subset, Sp, F.Id("B")), Call("IsBasis", h, F.Id("B")))))), sequence)));
        return Semigroup(Instance("Infinite", s, All("h", Nat(), All("A", Set(s), body))));
    }
}
