using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PackingDomatic;

internal sealed class PackingDomaticPathCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/bresar2026packingdomatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint occupancy and interior broadcast counts give a uniform lower bound on the palette.",
        H("A Counting Bound for Packing Domatic Colourings"),
        Blocks(
            Node("local-counting", "The palette lower bound", "local_counting",
                CountingFormula(),
                "Suppose P_n has a packing k-domatic colouring with colours at most t and n at least "
                    + "t+1. Let E be the vertices whose broadcasts reach vertex 0. Each partition class "
                    + "contributes a vertex to E, and the colours on E are distinct, so k is at most |E| "
                    + "and |E| is at most t. Put delta=t-|E| and d=t-k. If t is at least 16d+13, "
                    + "consider vertex z=8d+7 and put h=4d+3. At most t-h vertices of E reach z; at most "
                    + "delta+1 vertices outside E lie in the prefix 0 through t; and at most 2delta+1 "
                    + "vertices beyond that prefix reach z. The last bound follows by matching their "
                    + "distinct colours to missing endpoint colours or to endpoint vertices before z. "
                    + "These three bounds give fewer than k broadcasters at z, contradicting domination "
                    + "by all k classes. Consequently 16k is at most 15t+12.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula CountingFormula() =>
        Disp(ForAll("n", F.Id("Nat"), ForAll("k", F.Id("Nat"), ForAll("t", F.Id("Nat"),
            ForAll("f", Seq(Call("Fin", F.Id("n")), Sp, To, Sp, F.Id("Nat")),
                Implies(Call("IsPackingDomatic", F.Id("n"), F.Id("k"), F.Id("t"), F.Id("f")),
                    Implies(LessOrEqual(Add(F.Id("t"), D(1)), F.Id("n")),
                        LessOrEqual(Multiply(D(1, 6), F.Id("k")),
                            Add(Multiply(D(1, 5), F.Id("t")), D(1, 2))))))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
