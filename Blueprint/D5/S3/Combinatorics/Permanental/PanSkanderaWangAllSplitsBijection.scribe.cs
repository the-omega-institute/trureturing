using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsBijectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The target family consists of one-based permutation words whose entry parity equals their one-based position parity.",
        H("PanSkanderaWangAllSplitsBijection"),
        Blocks(
            Node("b", "B", "B",
                BFormula(),
                "Source, Section 7 (p. 145): “We call the set that consists of u = u₁⋯uₙ satisfying the above conditions 𝔅ₙ, i,e,” followed by “𝔅ₙ = {u ∈ 𝔖ₙ | u₁u₂⋯uₙ takes odd and even integers alternately and u₁ is odd}”. The target family consists of one-based permutation words whose entry parity equals their one-based position parity. The proof hk supplies the list index bound.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("f-injective", "f injective", "f_injective",
                finjectiveFormula(),
                "For every order at least four, the recursive map is injective on the literal source family. Recovering the maximum insertion position and the pair-swapped suffix reduces equality of outputs to equality at the preceding order.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("f-image-b", "f image B", "f_image_B",
                fimageBFormula(),
                "For every order at least four, the algorithm maps each source word to a word in the literal parity family. Pair swapping changes the parity offset on an even suffix, and reverse-complementation preserves the target family.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula BFormula() => Disp(
        All("n", Naturals(), All("x", Call("List", Naturals()), Iff(Call("B", F.Id("n"), F.Id("x")), And(Call("IsPerm", F.Id("n"), F.Id("x")), All("k", Naturals(), All("hk", LessThan(F.Id("k"), Call("length", F.Id("x"))), Equal(new Formula.Modulo(Call("getElem", F.Id("x"), F.Id("k"), F.Id("hk")), D(2)), new Formula.Modulo(Add(F.Id("k"), D(1)), D(2))))))))));

    private static Formula finjectiveFormula() => Disp(
        All("n", Naturals(), Implies(LessEqual(D(4), F.Id("n")), All("w", Call("List", Naturals()), All("z", Call("List", Naturals()), Implies(Call("A", F.Id("n"), F.Id("w")), Implies(Call("A", F.Id("n"), F.Id("z")), Implies(Equal(Call("f", F.Id("n"), F.Id("w")), Call("f", F.Id("n"), F.Id("z"))), Equal(F.Id("w"), F.Id("z"))))))))));

    private static Formula fimageBFormula() => Disp(
        All("n", Naturals(), Implies(LessEqual(D(4), F.Id("n")), All("w", Call("List", Naturals()), Implies(Call("A", F.Id("n"), F.Id("w")), Call("B", F.Id("n"), Call("f", F.Id("n"), F.Id("w"))))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
