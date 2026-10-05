using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBlock.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A permutation preserves a block exactly when membership before and after its action agrees at every index.",
        H("PanSkanderaWangAllSplitsBlock"),
        Blocks(
            Node("preserves", "Preserves", "Preserves",
                PreservesFormula(),
                "A permutation preserves a block exactly when membership before and after its action agrees at every index. The anonymous bracket is the Lean DecidableEq instance; alpha is an arbitrary type.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("blockequiv", "blockEquiv", "blockEquiv",
                blockEquivFormula(),
                "The forward defining expression extends the two subtype permutations by identity and multiplies them. The inverse defining expression restricts the block-preserving permutation to the block and its complement. val and property are the two subtype projections; the inverse laws are verified in Lean.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("permanent-block-expansion", "permanent block expansion", "permanent_block_expansion",
                permanentblockexpansionFormula(),
                "The product of the complementary principal permanents equals the sum over all block-preserving permutation monomials. The constructed block equivalence identifies the two independently chosen permutations with a single permutation of the whole index set.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula PreservesFormula() => Disp(
        All("alpha", Seq(F.Id("Type"), Star), Seq(OpenBracket, Call("DecidableEq", F.Id("alpha")), CloseBracket, Sp, All("s", Call("Finset", F.Id("alpha")), All("w", Call("Perm", F.Id("alpha")), Iff(Call("Preserves", F.Id("s"), F.Id("w")), All("i", F.Id("alpha"), Iff(Member(App(F.Id("w"), F.Id("i")), F.Id("s")), Member(F.Id("i"), F.Id("s"))))))))));

    private static Formula blockEquivFormula() => Disp(
        All("alpha", Seq(F.Id("Type"), Star), Seq(OpenBracket, Call("DecidableEq", F.Id("alpha")), CloseBracket, Sp, All("s", Call("Finset", F.Id("alpha")), And(All("sigma", Call("Perm", F.Id("s")), All("tau", Call("Perm", Call("Subtype", F.Id("alpha"), LambdaOf("i", F.Id("alpha"), Not(Member(F.Id("i"), F.Id("s")))))), Equal(Call("val", App(Call("blockEquiv", F.Id("s")), Call("pair", F.Id("sigma"), F.Id("tau")))), Multiply(Call("ofSubtype", F.Id("sigma")), Call("ofSubtype", F.Id("tau")))))), All("w", Call("Subtype", Call("Perm", F.Id("alpha")), LambdaOf("w", Call("Perm", F.Id("alpha")), Call("Preserves", F.Id("s"), F.Id("w")))), Equal(App(Call("symm", Call("blockEquiv", F.Id("s"))), F.Id("w")), Call("pair", Call("subtypePerm", Call("val", F.Id("w")), Call("property", F.Id("w"))), Call("subtypePerm", Call("val", F.Id("w")), LambdaOf("i", F.Id("alpha"), Call("notCongr", App(Call("property", F.Id("w")), F.Id("i")))))))))))));

    private static Formula permanentblockexpansionFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("s", Call("Finset", Call("Fin", F.Id("n"))), Equal(Multiply(Call("principalPermanent", F.Id("A"), F.Id("s")), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, F.Id("s")))), Call("sum", LambdaOf("w", Call("Subtype", Call("Perm", Call("Fin", F.Id("n"))), LambdaOf("v", Call("Perm", Call("Fin", F.Id("n"))), Call("Preserves", F.Id("s"), F.Id("v")))), Call("monomial", F.Id("A"), Call("val", F.Id("w"))))))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)),
            Sp, Mapsto, Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }}
