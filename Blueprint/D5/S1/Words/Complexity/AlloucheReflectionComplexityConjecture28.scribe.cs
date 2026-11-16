using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class AlloucheReflectionComplexityConjecture28Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/allouche2025reflectioncomplexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear factor complexity implies bounded integer reflection differences.",
        H("Bounded reflection differences for every word of linear complexity"),
        Blocks(
            Node("claim", "Conjecture 28: the bounded-difference assertion", Equal(Named("claim"), Parenthesized(ClaimBody())),
                "Conjecture 28, p. 15: “Let x be a sequence of at most linear factor complexity. Then rₓ(n+1)−rₓ(n) is bounded for all n ≥ 0. Hence, in particular, if x is (generalized) automatic, so is (rₓ(n+1)−rₓ(n))ₙ≥₀.” Here the proposition is the full bounded-difference assertion. The alphabet is any finite type, x is any one-sided word, and every length n includes zero. The hypothesis p(n) ≤ C(n + 1) expresses at most linear factor complexity. Differences are taken in ℤ before Int.natAbs. The source's automaticity sentence is outside this proposition; generalized numeration requires its addable positional-numeration hypotheses.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "Every such word has bounded reflection differences", ClaimBody(),
                "Place a new marker between the two sides of a bi-infinite mirror of x. Its factor count is the reversal-symmetrized count plus n. For a bi-infinite language, every fixed-offset cropping map is surjective. Weighted factor graphs then control intermediate excess using two lengths with small increments: a cut estimate forces heavy edges to return, and word overlap prevents two heavy outgoing edges. Linear growth supplies those two lengths by interval averaging. The resulting mirror increment bound transfers through reflection-orbit and palindromic-loop counts to the displayed absolute-difference bound. The same proof includes periodic words and transient prefixes. It supplies a finite bound without asserting optimal dependence on the growth coefficient.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("acls-reflection-complexity-c28"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("acls-c28-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Arrow(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Colon, Sp, Mathbb, Grp(F.Id("Z"))));

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A"), x = F.Id("x"), c = F.Id("C"), b = F.Id("B"), n = F.Id("n"), k = F.Id("k");
        Formula linear = Some(c, Nats(), All(k, Nats(), Le(
            Call("Finset.card", Call("wordFactorSet", x, k)), Mul(c, Add(k, D(1))))));
        Formula difference = Call("Int.natAbs", new Formula.Binary(
            Cast(Call("reflectionComplexity", x, Add(n, D(1)))), FormulaBinaryOperator.Subtract,
            Cast(Call("reflectionComplexity", x, n))));
        return All(a, Named("Type"), Seq(OpenBracket, Call("Fintype", a), CloseBracket, Sp,
            All(x, Fn(Nats(), a), Arrow(linear, Some(b, Nats(), All(n, Nats(), Le(difference, b)))))));
    }
}
