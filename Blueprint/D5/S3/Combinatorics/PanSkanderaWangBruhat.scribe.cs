using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class PanSkanderaWangBruhatDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PanSkanderaWangBruhat.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Pan-Skandera-Wang map raises every source permutation in the strong Bruhat order.",
        H("Pan-Skandera-Wang Bruhat Theorem"),
        Blocks(
            Node("ru-mem-a-of-long-prefix", "Reverse-complement source membership",
                "ru_mem_A_of_longPrefix", RuMemAFormula(),
                "For an odd size, a permutation whose initial long prefix is the initial interval becomes a member of A after reverse-complementation.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Pan-Skandera-Wang Bruhat theorem", "result", ResultFormula(),
                "The recursive map satisfies the Bruhat monotonicity claim for every size at least four, as proved by the selection invariant and the four base words.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("psw-bruhat-increasing-bijection"), ResolutionKind.Proved))),
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

    private static Formula RuMemAFormula() => Disp(ForAllMany(
        [Bound("m", Naturals()), Bound("a", ListType())],
        Implies(And(Call("IsPerm", F.Id("m"), F.Id("a")),
                Equal(Call("mod", F.Id("m"), D(2)), D(1)),
                Call("Perm", Call("take", F.Id("a"),
                        Add(Call("floorHalf", F.Id("m")), D(1))),
                    Call("rangePrime", D(1), Add(Call("floorHalf", F.Id("m")), D(1))))),
            Call("A", F.Id("m"), Call("RU", F.Id("m"), F.Id("a"))))));

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula ListType() => Call("List", Naturals());
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);
    private static Formula ForAllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
