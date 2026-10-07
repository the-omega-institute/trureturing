using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsWordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ListOfFn lists the function values in increasing Fin order.",
        H("PanSkanderaWangAllSplitsWord"),
        Blocks(
            Node("word", "word", "word",
                wordFormula(),
                "ListOfFn lists the function values in increasing Fin order. Adding one converts the zero-based permutation to the paper's one-based word.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("ofword", "ofWord", "ofWord",
                ofWordFormula(),
                "ofWord is Equiv.ofBijective of the function i mapped to the Fin n value x[val i] - 1. The displayed equation is its defining value expression; getElem uses the index bound obtained from hx. Permutation membership gives positive bounded entries and verifies injectivity and surjectivity. Subtraction on natural numbers is truncated.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula wordFormula() => Disp(
        All("n", Naturals(), All("w", Call("Perm", Call("Fin", F.Id("n"))), Equal(Call("word", F.Id("w")), Call("ListOfFn", LambdaOf("i", Call("Fin", F.Id("n")), Add(Call("val", App(F.Id("w"), F.Id("i"))), D(1))))))));

    private static Formula ofWordFormula() => Disp(
        All("n", Naturals(), All("x", Call("List", Naturals()), All("hx", Call("IsPerm", F.Id("n"), F.Id("x")), All("i", Call("Fin", F.Id("n")), Equal(Call("val", App(Call("ofWord", F.Id("x"), F.Id("hx")), F.Id("i"))), Subtract(Call("getElem", F.Id("x"), Call("val", F.Id("i"))), D(1))))))));
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

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
