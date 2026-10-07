using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsPaddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPadding.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The defining FinCases expression places one in the new first diagonal position, zero in the rest of its row and column, and A in the remaining block.",
        H("PanSkanderaWangAllSplitsPadding"),
        Blocks(
            Node("padone", "padOne", "padOne",
                padOneFormula(),
                "The defining FinCases expression places one in the new first diagonal position, zero in the rest of its row and column, and A in the remaining block. FinCases uses the zero and successor branches; const(0) is the anonymous constant-zero function.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tnn-padone", "tnn padOne", "tnn_padOne",
                tnnpadOneFormula(),
                "Adding the first identity entry preserves every increasing square minor. A minor selecting both first indices reduces to the old minor; selecting only one gives a zero row or column; selecting neither gives an old minor of the same size.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("padleft", "padLeft", "padLeft",
                padLeftFormula(),
                "Repeated left padding is defined by these two recursion equations. After d steps the matrix has order n+d.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tnn-padleft", "tnn padLeft", "tnn_padLeft",
                tnnpadLeftFormula(),
                "Every number of left identity-padding steps preserves the literal ordered-minor predicate, by induction on the number of steps.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula padOneFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("i", Call("Fin", Add(F.Id("n"), D(1))), All("j", Call("Fin", Add(F.Id("n"), D(1))), Equal(App(Call("padOne", F.Id("A")), F.Id("i"), F.Id("j")), Call("FinCases", Call("FinCases", D(1), Call("const", D(0)), F.Id("j")), LambdaOf("x", Call("Fin", F.Id("n")), Call("FinCases", D(0), LambdaOf("y", Call("Fin", F.Id("n")), App(F.Id("A"), F.Id("x"), F.Id("y"))), F.Id("j"))), F.Id("i"))))))));

    private static Formula tnnpadOneFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Implies(Call("TNN", F.Id("A")), Call("TNN", Call("padOne", F.Id("A")))))));

    private static Formula padLeftFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), And(Equal(Call("padLeft", F.Id("A"), D(0)), F.Id("A")), All("d", Naturals(), Equal(Call("padLeft", F.Id("A"), Add(F.Id("d"), D(1))), Call("padOne", Call("padLeft", F.Id("A"), F.Id("d")))))))));

    private static Formula tnnpadLeftFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Implies(Call("TNN", F.Id("A")), All("d", Naturals(), Call("TNN", Call("padLeft", F.Id("A"), F.Id("d"))))))));
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

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }}
