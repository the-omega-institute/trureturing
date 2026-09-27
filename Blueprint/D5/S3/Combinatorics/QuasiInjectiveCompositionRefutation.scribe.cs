using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class QuasiInjectiveCompositionRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pongsriiam2021quasi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squaring and collapsing the squares are quasi-injective while their composite is not.",
        H("Quasi-Injectivity Is Not Closed Under Composition"),
        Blocks(
            Node("quasi-injective-definition", "Quasi-injectivity", "QuasiInjective",
                QuasiInjectiveFormula(),
                "Definition 1 of the source reads verbatim: \"We call a function f : N to C a "
                    + "quasi-injective function if for all a, b in N, the condition "
                    + "f(an) = f(bn) for all n in N implies a = b.\" The source works with the "
                    + "positive integers, so the quantifiers over a, b and n carry positivity. "
                    + "The condition is weaker than injectivity: it only asks that the whole "
                    + "family of values on the multiples of a determine a.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("square-definition", "Squaring", "square",
                SquareFormula(),
                "The inner factor of the counterexample. It is injective, hence quasi-injective, "
                    + "and it is completely multiplicative; it is not surjective, which is why "
                    + "it does not meet the sufficient condition the source names.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("collapse-definition", "Collapsing the squares", "collapse",
                CollapseFormula(),
                "The outer factor of the counterexample: every perfect square is sent to one "
                    + "and every other value is left alone. The test is written with the "
                    + "natural-number square root, which squares back to the input exactly on "
                    + "the perfect squares.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("composition-question", "The question asked of composites", "claim",
                ClaimFormula(),
                "The first question of Question 19 of the source reads verbatim: \"Suppose f "
                    + "and g are quasi-injective. Is the composition f o g quasi-injective?\" "
                    + "The statement displayed here is the affirmative reading. The source adds "
                    + "that an obvious sufficient condition for the composite to be "
                    + "quasi-injective is that g is both surjective and completely "
                    + "multiplicative, and asks whether a weaker condition exists; that "
                    + "classification question is separate and is not addressed here.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("composition-refuted", "Composites need not be quasi-injective", "result",
                ResultFormula(),
                "The answer is no. Squaring is quasi-injective because agreement at n equal to "
                    + "one already gives a squared equal to b squared. Collapsing the squares "
                    + "is quasi-injective for a different reason: given distinct positive a and "
                    + "b, choose a prime p larger than their product, so p divides neither. If "
                    + "a times p were a square, say k times k, then p would divide k times k "
                    + "and hence k, so p squared would divide a times p and p would divide a, "
                    + "which it does not; so a times p is not a square, and neither is b times "
                    + "p, whence the two values are a times p and b times p and they differ. "
                    + "But the composite sends every n to the collapse of n times n, which is "
                    + "one; so it agrees on the multiples of one and on the multiples of two "
                    + "while one and two differ, and it is not quasi-injective.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("quasi-injective-composition-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula QuasiInjectiveFormula()
    {
        Formula f = F.Id("f"), a = F.Id("a"), b = F.Id("b"), n = F.Id("n");
        Formula agree = Universal("n", Naturals(),
            Implies(LessEqual(D(1), n),
                Equal(Call("f", Multiply(a, n)), Call("f", Multiply(b, n)))));
        Formula body = Universal("a", Naturals(),
            Universal("b", Naturals(),
                Implies(LessEqual(D(1), a),
                    Implies(LessEqual(D(1), b),
                        Implies(agree, Equal(a, b))))));
        return Disp(Universal("f", Functions(),
            Iff(Call("QuasiInjective", f), body)));
    }

    private static Formula SquareFormula()
    {
        Formula n = F.Id("n");
        return Disp(Universal("n", Naturals(),
            Equal(Call("square", n), Multiply(n, n))));
    }

    private static Formula CollapseFormula()
    {
        Formula n = F.Id("n");
        Formula root = Call("sqrt", n);
        Formula isSquare = Equal(Multiply(root, root), n);
        return Disp(Universal("n", Naturals(),
            And(Implies(isSquare, Equal(Call("collapse", n), D(1))),
                Implies(Negated(isSquare), Equal(Call("collapse", n), n)))));
    }

    private static Formula ClaimFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g");
        Formula body = Universal("f", Functions(),
            Universal("g", Functions(),
                Implies(Call("QuasiInjective", f),
                    Implies(Call("QuasiInjective", g),
                        Call("QuasiInjective", Seq(f, Sp, Circ, Sp, g))))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Functions() =>
        Seq(Naturals(), Sp, To, Sp, Naturals());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Negated(Formula value) =>
        new Formula.Not(Parenthesized(value));

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
