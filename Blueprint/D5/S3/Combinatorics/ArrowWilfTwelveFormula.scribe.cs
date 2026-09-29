using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwelveFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwelveFormula.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first avoidance class is counted by the finite formula F1.",
        H("Counting the First Arrow-Pattern Avoiders"),
        Blocks(
            Node("twelve-fiber-equivalence", "The largest-fixed-point fiber", "twelveFiberEquiv", null,
                "For each support value m, the avoiding words whose largest hat-fixed entry is m are equivalent to the disjoint union of TwelveData(n,m,k) over k from zero through n minus m.", DescribeRole.Definition),
            Node("twelve-count", "The first avoidance formula", "card_twelve_avoiders", CountFormula(),
                "For every positive n, the set cardinality of the first arrow-pattern avoidance class equals F1(n). The no-fixed-point stratum contributes the derangement number; each largest-fixed-point fiber contributes its decorated-object count.", DescribeRole.Theorem)),
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
            Seq(OpenBracket, D(1), Comma, Sp, D(2), CloseBracket),
            Seq(OpenBracket, Open, D(3), Comma, Sp, D(3), Close, CloseBracket), D(3)));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
            new Formula.Logic(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies,
                new Formula.Relation(left, FormulaRelationOperator.Equal, Call("F1", n)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
