using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwentyThreeFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwentyThreeFormula.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second avoidance class is counted by the finite formula F2.",
        H("Counting the Second Arrow-Pattern Avoiders"),
        Blocks(
            Node("twenty-three-word-equivalence", "Avoiders as words on the standard support", "avoiderWordEquiv", null,
                "For each n, the set of lists avoiding (23; 1 to 1) is equivalent to the subtype of words on the support from one through n that do not contain this pattern.", DescribeRole.Definition),
            Node("twenty-three-count", "The second avoidance formula", "card_twentyThree_avoiders", CountFormula(),
                "For every positive n, the set cardinality of the second arrow-pattern avoidance class equals F2(n). The no-fixed-point stratum, the stratum fixed only at n, and the smaller-minimum fibers give its three terms.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula CountFormula()
    {
        var n = F.Id("n");
        var left = Call("ncard", Call("avoiders", n,
            Seq(OpenBracket, D(2), Comma, Sp, D(3), CloseBracket),
            Seq(OpenBracket, Open, D(1), Comma, Sp, D(1), Close, CloseBracket), D(3)));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
            new Formula.Logic(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies,
                new Formula.Relation(left, FormulaRelationOperator.Equal, Call("F2", n)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
