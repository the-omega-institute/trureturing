using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class PanSkanderaWangAllSplitsPermanentPaddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsPermanentPadding.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The defining filter pulls an index set back along Fin.succ, extracting precisely its old matrix indices..",
        H("PanSkanderaWangAllSplitsPermanentPadding"),
        Blocks(
            Node("oldindices", "oldIndices", "oldIndices",
                oldIndicesFormula(),
                "The defining filter pulls an index set back along Fin.succ, extracting precisely its old matrix indices.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("principal-padone", "principal padOne", "principal_padOne",
                principalpadOneFormula(),
                "Every selected principal permanent loses only the newly adjoined identity coordinate. If that coordinate is present, decomposing permutations of an Option type leaves precisely the permutations that fix it; all other summands contain a zero entry.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("splitproduct", "splitProduct", "splitProduct",
                splitProductFormula(),
                "This is the product of the two complementary principal permanents for the literal initial split.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("parityproduct", "parityProduct", "parityProduct",
                parityProductFormula(),
                "This is the product of the principal permanents on the even and odd one-based indices.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("split-padleft", "split padLeft", "split_padLeft",
                splitpadLeftFormula(),
                "After d left identity coordinates, the split at h+d has the same permanent product as the original split at h. Induction tracks the literal initial index set through each padding step.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("parity-padleft", "parity padLeft", "parity_padLeft",
                paritypadLeftFormula(),
                "Left identity padding preserves the alternating permanent product. Each step swaps the two old parity classes, and multiplication makes the product invariant under that swap.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula oldIndicesFormula() => Disp(
        All("n", Naturals(), All("s", Call("Finset", Call("Fin", Add(F.Id("n"), D(1)))), Equal(Call("oldIndices", F.Id("s")), Call("filter", Call("univ", Call("Fin", F.Id("n"))), LambdaOf("i", Call("Fin", F.Id("n")), Member(Call("succ", F.Id("i")), F.Id("s"))))))));

    private static Formula principalpadOneFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("s", Call("Finset", Call("Fin", Add(F.Id("n"), D(1)))), Equal(Call("principalPermanent", Call("padOne", F.Id("A")), F.Id("s")), Call("principalPermanent", F.Id("A"), Call("oldIndices", F.Id("s"))))))));

    private static Formula splitProductFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("h", Naturals(), Equal(Call("splitProduct", F.Id("A"), F.Id("h")), Multiply(Call("principalPermanent", F.Id("A"), Call("prefixIndices", F.Id("n"), F.Id("h"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("prefixIndices", F.Id("n"), F.Id("h"))))))))));

    private static Formula parityProductFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), Equal(Call("parityProduct", F.Id("A")), Multiply(Call("principalPermanent", F.Id("A"), Call("evenIndices", F.Id("n"))), Call("principalPermanent", F.Id("A"), Seq(Call("univ", Call("Fin", F.Id("n"))), Sp, Setminus, Sp, Call("evenIndices", F.Id("n")))))))));

    private static Formula splitpadLeftFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("d", Naturals(), All("h", Naturals(), Equal(Call("splitProduct", Call("padLeft", F.Id("A"), F.Id("d")), Add(F.Id("h"), F.Id("d"))), Call("splitProduct", F.Id("A"), F.Id("h"))))))));

    private static Formula paritypadLeftFormula() => Disp(
        All("n", Naturals(), All("A", Call("Matrix", Call("Fin", F.Id("n")), Call("Fin", F.Id("n")), Reals()), All("d", Naturals(), Equal(Call("parityProduct", Call("padLeft", F.Id("A"), F.Id("d"))), Call("parityProduct", F.Id("A")))))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

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

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
