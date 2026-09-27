using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwelveCardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwelveCard.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The decorated family has the binomial-product cardinality in the first avoidance formula.",
        H("Counting the First Decorated Family"),
        Blocks(
            Node("twelve-data-enough", "Counting when all required gaps fit", "card_twelveData_of_enough", CountFormula(true), "When the number of mandatory positive gaps does not exceed m minus one, the decorated-data cardinality is choose(n minus m,k) times choose(m plus k minus one,n minus m) times the k-th derangement number.", DescribeRole.Theorem),
            Node("twelve-data-cardinality", "Counting every decorated fiber", "card_twelveData", CountFormula(false), "For every natural n,m,k with m positive, the same binomial-product formula counts TwelveData(n,m,k); when mandatory gaps cannot fit, both sides vanish.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula CountFormula(bool requireEnough)
    {
        var n = F.Id("n"); var m = F.Id("m"); var k = F.Id("k");
        var left = Call("card", Call("TwelveData", n, m, k));
        var right = Mul(Call("choose", Sub(n, m), k), Call("numDerangements", k),
            Call("choose", Sub(Add(m, k), D(1)), Sub(n, m)));
        var statement = Imp(Le(D(1), m), Eq(left, right));
        if (requireEnough)
            statement = Imp(Le(D(1), m), Imp(
                Le(Sub(Call("card", Call("upperSupport", n, m)), k), Sub(m, D(1))),
                Eq(left, right)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("n"), Bound("m"), Bound("k")], statement));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), new Formula.NamedConstant(FormulaIdentifier.Create("Nat")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(params Formula[] args)
    {
        Formula result = args[0];
        for (var i = 1; i < args.Length; i++) result = new Formula.Binary(result, FormulaBinaryOperator.Multiply, args[i]);
        return result;
    }
}
