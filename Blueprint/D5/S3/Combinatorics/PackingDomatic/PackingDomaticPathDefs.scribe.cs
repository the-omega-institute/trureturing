using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PackingDomatic;

internal sealed class PackingDomaticPathDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/bresar2026packingdomatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Packing colourings and broadcast domination on finite paths.",
        H("Packing Domatic Colourings of Paths"),
        Blocks(
            Node("packing-domatic-colouring", "Packing and broadcast domination", "IsPackingDomatic",
                PackingFormula(),
                "The path P_n has vertices 0 through n-1 and distance d(u,v)=|u-v|. A colouring f "
                    + "uses the integers 1 through t. Distinct vertices of the same colour j have distance "
                    + "greater than j. A map A partitions the vertices into k classes: for every class i "
                    + "and every vertex x, some vertex a in class i satisfies d(x,a) at most f(a).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("problem-two", "The proposed palette bound", "claim",
                ClaimFormula(),
                "Problem 2 asks whether every path P_n with k at least 3 and n at least 2k has a "
                    + "packing k-domatic colouring using at most k+1 colours. Equivalently, it asks whether "
                    + "the packing k-domatic chromatic number of each such path is at most k+1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)))));

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

    private static Formula PackingFormula() =>
        Disp(Equivalent(Call("IsPackingDomatic", F.Id("n"), F.Id("k"), F.Id("t"), F.Id("f")),
            And(ForAll("v", Call("Fin", F.Id("n")),
                    And(LessOrEqual(D(1), Call("f", F.Id("v"))),
                        LessOrEqual(Call("f", F.Id("v")), F.Id("t")))),
                And(ForAll("u", Call("Fin", F.Id("n")),
                        ForAll("v", Call("Fin", F.Id("n")),
                            Implies(NotEqual(F.Id("u"), F.Id("v")),
                                Implies(Equal(Call("f", F.Id("u")), Call("f", F.Id("v"))),
                                    Less(Call("f", F.Id("u")), Call("d", F.Id("u"), F.Id("v"))))))),
                    ThereExists("A", Seq(Call("Fin", F.Id("n")), Sp, To, Sp, Call("Fin", F.Id("k"))),
                        ForAll("i", Call("Fin", F.Id("k")),
                            ForAll("x", Call("Fin", F.Id("n")),
                                ThereExists("a", Call("Fin", F.Id("n")),
                                    And(Equal(Call("A", F.Id("a")), F.Id("i")),
                                        LessOrEqual(Call("d", F.Id("x"), F.Id("a")),
                                            Call("f", F.Id("a"))))))))))));

    private static Formula ClaimFormula() =>
        Disp(Equivalent(F.Id("claim"), ForAll("k", F.Id("Nat"), ForAll("n", F.Id("Nat"),
            Implies(LessOrEqual(D(3), F.Id("k")),
                Implies(LessOrEqual(Multiply(D(2), F.Id("k")), F.Id("n")),
                    ThereExists("f", Seq(Call("Fin", F.Id("n")), Sp, To, Sp, F.Id("Nat")),
                        Call("IsPackingDomatic", F.Id("n"), F.Id("k"),
                            Add(F.Id("k"), D(1)), F.Id("f")))))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ThereExists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
