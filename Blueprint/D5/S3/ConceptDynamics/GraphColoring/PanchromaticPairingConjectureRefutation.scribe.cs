using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class PanchromaticPairingConjectureRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GraphColoring/"
            + "PanchromaticPairingConjectureRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/lalou2026completely");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A six-vertex hypergraph refutes the proposed equality between panchromatic and bipanchromatic extrema.",
        H("Refutation of the panchromatic pairing conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("panchromatic-pairing-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Lalou--Mbarek--Skender--Togni Conjecture 1"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a finite set-valued hypergraph, p and b are attained maxima over all "
                        + "panchromatic and bipanchromatic color counts. The value a is an attained "
                        + "minimum of the number of globally singleton color fibers over all "
                        + "maximizing p-colorings. The claim states b = p - ceil(a/2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("panchromatic-pairing-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Conjecture 1 is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "On vertices 0 through 5, take the three edges {0,1,2,3}, "
                        + "{0,1,2,4}, and {0,1,2,5}. Their panchromatic maximum is four. "
                        + "Every maximizing coloring has the three core colors globally singleton "
                        + "and a common petal color, so the minimum singleton count is three. "
                        + "The bipanchromatic maximum is three. Thus the left side is 3 while "
                        + "the proposed right side is 4 - ceil(3/2) = 2."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "lalou-mbarek-skender-togni-conjecture-one-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula()
    {
        Formula vertex = F.Id("V"), hypergraph = F.Id("H");
        Formula p = F.Id("p"), b = F.Id("b"), a = F.Id("a");
        Formula hypotheses = And(
            Call("IsPanchromaticMaximum", hypergraph, p),
            Call("IsBipanchromaticMaximum", hypergraph, b),
            Call("IsSingletonMinimum", hypergraph, p, a));
        Formula equality = Equal(b,
            Subtract(p, Call("ceilDiv", a, D(2))));
        Formula quantified = ForAllMany(
            [
                Bound("V", F.Id("FiniteType")),
                Bound("H", Call("Hypergraph", vertex)),
                Bound("p", Naturals()),
                Bound("b", Naturals()),
                Bound("a", Naturals())
            ],
            Implies(hypotheses, equality));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula And(params Formula[] values)
    {
        Formula result = Parenthesized(values[^1]);
        for (int index = values.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(values[index]),
                FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
