using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MendoncaMinPlusTriangleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MendoncaMinPlusTriangle.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/mendonca2026a400584");
    private const string NameQuote =
        "Irregular triangle read by rows: T(n,k) is the number of labelings of the internal vertices "
        + "of the complete plane binary tree of depth n by + or min, with every leaf equal to 1, "
        + "that evaluate to k at the root (n >= 1, 1 <= k <= 2^n).";
    private const string TreeQuote =
        "The tree has 2^n leaves and 2^n - 1 internal vertices. Each internal vertex applies its "
        + "operator to the values of its two children. Left and right positions are distinguished; "
        + "labelings related by exchanges of children are counted separately.";
    private const string ClaimQuote =
        "Auffinger and Cable report unpublished work of Albert Chen proving that the root-value "
        + "probabilities decrease with k, independently discovered by Tam Cheetham-West. Here "
        + "monotonicity must be understood in the weak sense, since the first two rows contain ties. "
        + "Conjecture: T(n,k) > T(n,k+1) for n >= 3 and 1 <= k < 2^n. This strict-monotonicity "
        + "conjecture has been verified by exact computation for 3 <= n <= 12, but is not proved in general.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict decrease of the min-plus configuration counts from depth three onward.",
        H("Mendonça's Min-Plus Configuration Triangle"),
        Blocks(
            Node("Op", "The two root operators", OpFormula(),
                NameQuote + " (OEIS A400584, NAME, revision 28; unpaginated.) "
                + "Op has exactly two constructors, Op.plus and Op.min, for addition and minimum.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("LabeledTree", "Ordered complete trees", TreeFormula(),
                TreeQuote + " (OEIS A400584, first COMMENT, revision 28; unpaginated.) "
                + "LabeledTree n records all internal labels at depth n. Its leaf has depth zero; "
                + "LabeledTree.node has an operator and two ordered subtrees of equal depth. "
                + "Thus exchanging unequal subtrees changes the counted labeling.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("value", "Root evaluation", ValueFormula(),
                NameQuote + " " + TreeQuote
                + " (OEIS A400584, NAME and first COMMENT, revision 28; unpaginated.) "
                + "The natural-valued recursion starts at one and applies the root operator.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("T", "The configuration count", CountFormula(),
                NameQuote + " (OEIS A400584, NAME, revision 28; unpaginated.) "
                + "Nat.card counts the finite subtype of labeled trees with the specified root value; "
                + "natural depth zero extends the same tree definition to a single leaf.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", "Strict-monotonicity conjecture", Disp(Iff(F.Id("claim"), Parenthesized(ClaimBody()))),
                ClaimQuote + " (OEIS A400584, fourth COMMENT, revision 28; unpaginated.) "
                + "Both indices are natural numbers. The inequalities retain every depth at least "
                + "three and each adjacent pair of columns from one through two to the depth.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "Strict decrease at every depth from three", Disp(ClaimBody()),
                "For every natural depth n at least three and column k with 1 ≤ k < 2^n, "
                + "T n (k+1) is strictly less than T n k. Splitting a labeled tree into its root "
                + "operator and ordered subtrees gives the min-plus counting recurrence. "
                + "Its adjacent differences decompose into nonnegative products. A product is "
                + "strictly positive below, at, and above the old support endpoint. "
                + "Consequently the transform preserves strict decrease for positive strictly "
                + "decreasing integer inputs of finite support length at least two. "
                + "The row at depth three starts the induction. The source's support and "
                + "recurrence retain their meanings; the strict conclusion strengthens weak decrease.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role) => Describe.Lean(
            DescribeId.Create("mendonca-min-plus-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula OpFormula() => Disp(new Formula.Aligned([
        Typed(F.Id("Op"), F.Id("Type")),
        Typed(Q("Op", "plus"), F.Id("Op")),
        Typed(Q("Op", "min"), F.Id("Op"))]));

    private static Formula TreeFormula()
    {
        Formula n = F.Id("n");
        Formula op = F.Id("op");
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        return Disp(new Formula.Aligned([
            Typed(F.Id("LabeledTree"), new Formula.TypeArrow(Nat(), F.Id("Type"))),
            Typed(Q("LabeledTree", "leaf"), Call("LabeledTree", D(0))),
            All([B("n", Nat()), B("op", F.Id("Op")),
                B("left", Call("LabeledTree", n)), B("right", Call("LabeledTree", n))],
                Typed(App(Q("LabeledTree", "node"), op, left, right),
                    Call("LabeledTree", Add(n, D(1)))))]));
    }

    private static Formula ValueFormula()
    {
        Formula n = F.Id("n");
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        Formula NodeValue(string op) => Call("value",
            App(Q("LabeledTree", "node"), Q("Op", op), left, right));
        return Disp(new Formula.Aligned([
            Equal(Call("value", Q("LabeledTree", "leaf")), D(1)),
            All([B("n", Nat()), B("left", Call("LabeledTree", n)), B("right", Call("LabeledTree", n))],
                Equal(NodeValue("plus"), Add(Call("value", left), Call("value", right)))),
            All([B("n", Nat()), B("left", Call("LabeledTree", n)), B("right", Call("LabeledTree", n))],
                Equal(NodeValue("min"), Call("min", Call("value", left), Call("value", right))))]));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula t = F.Id("t");
        Formula subtype = Seq(OpenBrace, t, Sp, Colon, Sp, Call("LabeledTree", n), Sp,
            Slash, Slash, Sp, Equal(Call("value", t), k), CloseBrace);
        return Disp(All([B("n", Nat()), B("k", Nat())],
            Equal(Call("T", n, k), App(Q("Nat", "card"), subtype))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        return All([B("n", Nat()), B("k", Nat())],
            Implies(Le(D(3), n), Implies(Le(D(1), k),
                Implies(Lt(k, new Formula.Power(D(2), n)),
                    Lt(Call("T", n, Add(k, D(1))), Call("T", n, k))))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] binders, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot,
        Operatorname, Grp(F.Id(name)));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
