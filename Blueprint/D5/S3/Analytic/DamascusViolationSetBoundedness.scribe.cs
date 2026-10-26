using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class DamascusViolationSetBoundednessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/DamascusViolationSetBoundedness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/sujsuntinukulchesneau2026damascus");
    private const string Question =
        "Section 5, page 19: “In addition to the above, it is natural to ask whether analogous structural properties hold for I_n^m when m is arbitrary. Can one prove or disprove that I_n^m (i) stays uniformly away from 1, (ii) is bounded, or (iii) forms an increasing family in n?” The source concludes: “Thus this question, together with question (iii), remains open.”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive product-one Damascus violation sets have a complete boundedness classification.",
        H("Boundedness of the Damascus violation sets"),
        Blocks(
            Node("term", "The Damascus summand", DescribeRole.Definition,
                All("n", Nat(), All("x", Real(), Equal(Call("term", X("n"), X("x")),
                    new Formula.Fraction(Sub(Pow(X("x"), X("n")), D(1)),
                        Add(Pow(X("x"), Add(X("n"), D(1))), D(1)))))),
                AssessedProvenance.FromLiterature(Source),
                "Inequality (1), page 2: “S_n^m(x₁, …, x_m) := Σ_{j=1}^m (x_jⁿ − 1)/(x_j^{n+1} + 1) ⩽ 0”. The function term is its real summand, with natural exponent n. Real division is total; the denominator is positive at every positive x."),
            Node("H", "Positive tuples with product one", DescribeRole.Definition,
                All("m", Nat(), Equal(Call("H", X("m")), SetOf(
                    And(All("j", Indices(), Less(D(0), Call("x", X("j")))),
                        Equal(Product(Call("x", X("j"))), D(1)))))),
                AssessedProvenance.FromLiterature(Source),
                "Page 2 defines “H_m := {(x₁, …, x_m) ∈ (0, +∞)^m : ∏_{j=1}^m x_j = 1}”. Coordinates are functions Fin m → ℝ, indexed from zero in Lean; each coordinate occurs once in the product."),
            Node("I", "The strict violation set", DescribeRole.Definition,
                All("n", Nat(), All("m", Nat(), Equal(Call("I", X("n"), X("m")),
                    SetOf(And(new Formula.Relation(X("x"), FormulaRelationOperator.MemberOf,
                        Call("H", X("m"))), Less(D(0), Sum(Call("term", X("n"), Call("x", X("j")))))))))),
                AssessedProvenance.FromLiterature(Source),
                "Section 5, page 13: “I_n^m := {(x₁, …, x_m) ∈ H_m : Σ_{j=1}^m (x_jⁿ − 1)/(x_j^{n+1} + 1) > 0}. For instance, we know that I_n^2 = ∅ for all n, and (1/2, 3/2, 4/3) ∈ I_n^3 for n ⩾ 5.” The function I uses the strict real inequality and the product-one set H, with a sum over Fin m."),
            Node("claim", "The answer to the boundedness question", DescribeRole.Definition,
                Equal(X("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Question + " The answer is quantified over positive natural dimensions and exponents. Boundedness uses Bornology.IsBounded on Fin m → ℝ. It holds precisely for m ≤ 3, for m = 4 with n ≤ 4, and for m = 5 or 6 with n = 1."),
            Node("result", "The complete classification", DescribeRole.Theorem,
                ClaimBody(), AssessedProvenance.FromRepo(Source),
                "For a positive coordinate x the summand lies strictly above −1 and strictly below 1/x. For x ≤ 1, term(n,x) + 1 ≤ 2x. Uniform bounds strictly below 1, together with term(1,x) ≤ 5/24 and term(4,x) ≤ 4999/10000, give confinement in the stated cases. If a coordinate exceeds K^(m−1), the product-one identity forces another below 1/K; these two coordinates and the remaining m−2 scalar bounds make the sum negative. In the other cases the tuple (t, 1/(t r^k), r, …, r), k = m−2, has product one and a strictly positive sum for every t > 1. Use r = 2 for n ≤ 4 and r = 3/2 for n ≥ 5. At (m,n) = (5,2) the middle summands sum exactly to 1; the two other summands sum strictly above −1. Thus this equality case is unbounded as well. The source's nesting question and separation from coordinate-one planes in arbitrary dimension are separate questions."))));

    private static DocumentBlock Node(string name, string title, DescribeRole role,
        Formula formula, AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create("damascus-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("sujsuntinukul-chesneau-2026-damascus-violation-set-question-ii"),
                ResolutionKind.Proved) : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Indices() => Call("Fin", X("m"));
    private static Formula SetOf(Formula condition) => Seq(OpenBrace, X("x"), Sp, Colon, Sp,
        Indices(), Sp, To, Sp, Real(), Sp, Bar, Sp, Parenthesized(condition), CloseBrace);
    private static Formula Product(Formula body) => Seq(Prod, Underscore,
        Grp(Seq(X("j"), Sp, Colon, Sp, Indices())), Sp, body);
    private static Formula Sum(Formula body) => Seq(F.Sum, Underscore,
        Grp(Seq(X("j"), Sp, Colon, Sp, Indices())), Sp, body);
    private static Formula ClaimBody()
    {
        var cells = Or(Leq(X("m"), D(3)), Or(And(Equal(X("m"), D(4)), Leq(X("n"), D(4))),
            And(Or(Equal(X("m"), D(5)), Equal(X("m"), D(6))), Equal(X("n"), D(1)))));
        var bounded = new Formula.Apply(Seq(Operatorname, Grp(Seq(X("Bornology"), Dot, X("IsBounded")))),
            [Call("I", X("n"), X("m"))]);
        return All("m", Nat(), All("n", Nat(), Imp(Leq(D(1), X("m")),
            Imp(Leq(D(1), X("n")), new Formula.Logic(Parenthesized(bounded),
                FormulaLogicOperator.Iff, Parenthesized(cells))))));
    }
}
