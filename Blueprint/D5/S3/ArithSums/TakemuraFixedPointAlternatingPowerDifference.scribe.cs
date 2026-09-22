using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class TakemuraFixedPointAlternatingPowerDifferenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.";
    private static readonly LibraryNoteRef SourceNote =
        LibraryNoteRef.Create("D5/L/ArithSums/takemura2025apd");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Takemura's fixed-point alternating power difference has first degree n - 1 and value n!.",
        H("Takemura's fixed-point alternating power difference"),
        Blocks(
            Node(
                "apd",
                "The alternating power difference",
                ApdFormula(),
                "Definition 1 (Alternating Power Difference). For an integer-valued "
                    + "function f : Sₙ → ℤ and m ≥ 1, we define: APDₘ(f) := "
                    + "Σ_{σ∈Sₙ} sgn(σ)f(σ)^m. (arXiv:2512.18169v1, printed p. 1.) "
                    + "The formal sum ranges over Equiv.Perm (Fin n), and the sign "
                    + "is cast to integers.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(SourceNote)),
            Node(
                "fix",
                "The fixed-point function",
                FixFormula(),
                "For a permutation σ ∈ Sₙ, let P_σ be the permutation matrix "
                    + "corresponding to σ. We define the function f_A : Sₙ → ℤ "
                    + "corresponding to matrix A as the trace of the product of matrix A "
                    + "and the permutation matrix P_σ. f_A(σ) := tr(AP_σ) = "
                    + "Σ_{i=1}^{n} A_{i,σ(i)}. (arXiv:2512.18169v1, printed p. 2.) "
                    + "Therefore, the value of this function is exactly equal to the total "
                    + "number of fixed points in the permutation σ. We define this function "
                    + "as the Fixed Point Function fix (or Fix point function). "
                    + "fix(σ) := f_{Iₙ}(σ). (arXiv:2512.18169v1, printed p. 3.) "
                    + "The formal expression is the filtered cardinality of the fixed indices.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(SourceNote)),
            Node(
                "firstAppearanceDegree",
                "The first appearance degree",
                FirstAppearanceDegreeFormula(),
                "Definition 2 (First Appearance Degree). For a function f : Sₙ → ℤ, "
                    + "the smallest m ≥ 1 such that APDₘ(f) ≠ 0 is called the First "
                    + "Appearance Degree (or APD Index) of f, denoted by m₁(f). "
                    + "If APDₘ(f) = 0 for all m ≥ 1, we define m₁(f) = ∞. "
                    + "(arXiv:2512.18169v1, printed p. 1.) The formal natural number "
                    + "is the sInf of exactly the defining set of positive indices with "
                    + "nonzero alternating power difference.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(SourceNote)),
            Node(
                "resultDegree",
                "Conjecture 1: first appearance degree",
                ResultDegreeFormula(),
                "Conjecture 1 (First Appearance Degree of Identity Matrix). For n ≥ 2, "
                    + "the first appearance degree m₁(Iₙ) of the fixed point function fix "
                    + "corresponding to the n-th order identity matrix Iₙ is given by the "
                    + "following closed form: m₁(Iₙ) = n − 1. This relationship has been "
                    + "verified for n ≤ 10. (arXiv:2512.18169v1, printed p. 4.) "
                    + "The statement is the source's conjecture, which it verifies numerically "
                    + "for n ≤ 10 and leaves unproved; the proof is repository-derived. "
                    + "The proof expands fix(sigma)^m over tuples of indices, exchanges the "
                    + "finite sums, evaluates the signed sum over permutations fixing the "
                    + "tuple image pointwise, and uses the resulting vanishing range together "
                    + "with the first nonzero injection count to identify the least degree.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(SourceNote),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("takemura-fixed-point-apd-conjecture-1"),
                    ResolutionKind.Proved)),
            Node(
                "resultValue",
                "Conjecture 2: first appearance value",
                ResultValueFormula(),
                "Conjecture 2 (Formula for First Appearance Value of Identity Matrix). "
                    + "For n ≥ 2, the first appearance value APDₙ₋₁(Iₙ) of the fixed point "
                    + "function fix corresponding to the n-th order identity matrix Iₙ is "
                    + "given by the following closed form: APDₙ₋₁(Iₙ) = n!. This relationship "
                    + "has been verified for n ≤ 10. (arXiv:2512.18169v1, printed p. 4.) "
                    + "The statement is the source's conjecture, which it verifies numerically "
                    + "for n ≤ 10 and leaves unproved; the proof is repository-derived. "
                    + "The proof leaves exactly the injective maps from Fin(n-1) "
                    + "to Fin(n) after the pointwise-fixing sign sum, counts those embeddings, "
                    + "and simplifies the descending factorial to n!.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(SourceNote),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("takemura-fixed-point-apd-conjecture-2"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("takemura-apd-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        provenance,
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula ApdFormula()
    {
        var n = F.Id("n");
        var f = F.Id("f");
        var m = F.Id("m");
        var sigma = F.Id("sigma");
        var permutation = Perm(Fin(n));
        var functionType = new Formula.TypeArrow(permutation, Integers());
        var summand = Multiply(
            IntegerCast(PermSign(sigma)),
            new Formula.Power(new Formula.Apply(F.Id("f"), [sigma]), m));
        var sum = SumOver(sigma, permutation, summand);
        var equation = Equal(Call("apd", n, f, m), sum);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
             new Formula.BoundVariable(FormulaIdentifier.Create("f"), functionType),
             new Formula.BoundVariable(FormulaIdentifier.Create("m"), Naturals())],
            equation));
    }

    private static Formula FixFormula()
    {
        var n = F.Id("n");
        var sigma = F.Id("sigma");
        var i = F.Id("i");
        var equality = Equal(new Formula.Apply(F.Id("sigma"), [i]), i);
        var predicate = Parenthesized(Seq(LambdaLower, Sp, i, Sp, Mapsto, Sp, equality));
        var univ = Seq(F.Id("Finset"), Dot, F.Id("univ"));
        var filtered = new Formula.Apply(Seq(univ, Dot, F.Id("filter")), [predicate]);
        var right = IntegerCast(Call("card", filtered));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
             new Formula.BoundVariable(FormulaIdentifier.Create("sigma"), Perm(Fin(n)))],
            Equal(Call("fix", sigma), right)));
    }

    private static Formula FirstAppearanceDegreeFormula()
    {
        var n = F.Id("n");
        var f = F.Id("f");
        var m = F.Id("m");
        var condition = Parenthesized(And(
            Leq(D(1), m),
            Neq(Call("apd", n, f, m), D(0))));
        var candidates = SetOf(m, condition);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
             new Formula.BoundVariable(FormulaIdentifier.Create("f"),
                 new Formula.TypeArrow(Perm(Fin(n)), Integers()))],
            Equal(Call("firstAppearanceDegree", n, f), Call("sInf", candidates))));
    }

    private static Formula ResultDegreeFormula()
    {
        var n = F.Id("n");
        var conclusion = Equal(
            Call("firstAppearanceDegree", n, F.Id("fix")),
            Subtract(n, D(1)));
        return Disp(Universal("n", Naturals(),
            Implies(Parenthesized(Leq(D(2), n)), Parenthesized(conclusion))));
    }

    private static Formula ResultValueFormula()
    {
        var n = F.Id("n");
        var conclusion = Equal(
            Call("apd", n, F.Id("fix"), Subtract(n, D(1))),
            IntegerCast(Call("factorial", n)));
        return Disp(Universal("n", Naturals(),
            Implies(Parenthesized(Leq(D(2), n)), Parenthesized(conclusion))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Perm(Formula type) => QualifiedCall("Equiv", "Perm", type);
    private static Formula PermSign(Formula sigma) =>
        new Formula.Apply(Seq(F.Id("Equiv"), Dot, F.Id("Perm"), Dot, F.Id("sign")), [sigma]);
    private static Formula QualifiedCall(string prefix, string name, params Formula[] args) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, domain)), Sp, body);
    private static Formula SetOf(Formula variable, Formula condition) =>
        Seq(OpenBrace, variable, Colon, Sp, Naturals(), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula IntegerCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Integers()));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Neq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
