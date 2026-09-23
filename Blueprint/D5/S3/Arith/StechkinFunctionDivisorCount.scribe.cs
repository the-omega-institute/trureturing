using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class StechkinFunctionDivisorCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/StechkinFunctionDivisorCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/israeloudra2020a274010");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Stechkin function counts a divisibility condition that splits into divisors of two adjacent integers.",
        H("The Stechkin Function Divisor-Count Formula"),
        Blocks(
            Paragraph(Text(
                "All variables take values in the natural numbers N. The operator NatDiv "
                    + "is Euclidean natural-number division, so it is the floor of the "
                    + "corresponding nonnegative rational quotient. The operator Icc gives "
                    + "a closed finite interval, filter retains the elements satisfying its "
                    + "predicate, and card denotes finite-set cardinality.")),
            Node(
                "stechkin-function",
                "stechkinFunction",
                "The Stechkin counting function",
                StechkinFunctionFormula(),
                "For each n, the function counts exactly the integers m from two through n "
                    + "for which m-1 divides the Euclidean quotient of n(m-1) by m.",
                DescribeRole.Definition),
            Node(
                "adjacent-divisor-count-formula",
                "result",
                "The adjacent divisor-count identity",
                ResultFormula(),
                "For n at least two, reindexing by k=m-1 turns the filtered predicate into "
                    + "the disjoint union of the nontrivial divisors of n and n-1. Each full "
                    + "divisor set also contains one, so restoring those two omitted elements "
                    + "gives the displayed equality.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a274010-stechkin-divisor-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id,
        string declaration,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula StechkinFunctionFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula predecessor = Subtract(m, D(1));
        Formula quotient = Call("NatDiv", Multiply(n, predecessor), m);
        Formula predicate = Divides(predecessor, quotient);
        Formula filtered = Call("filter", Call("Icc", D(2), n), Lambda(m, predicate));
        return Universal("n", Equal(Call("stechkinFunction", n), Call("card", filtered)));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula premise = LessEqual(D(2), n);
        Formula left = Add(Call("stechkinFunction", n), D(2));
        Formula right = Add(
            Call("card", Call("divisors", n)),
            Call("card", Call("divisors", Subtract(n, D(1)))));
        return Universal("n", Implies(premise, Equal(left, right)));
    }

    private static Formula Universal(string name, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
            body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(binder, Sp, Mapsto, Sp, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
