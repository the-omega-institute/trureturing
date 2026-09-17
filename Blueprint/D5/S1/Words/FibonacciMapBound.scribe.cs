using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class FibonacciMapBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/FibonacciMapBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/joshirust2025monochromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bound the longest monochromatic arithmetic progression in the infinite Fibonacci word.",
        H("Fibonacci Word Progression Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-map-global-maximum"),
                DeclarationHandle.Create(Prefix + "goldenMAPMaximum"),
                H("The global maximum length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural difference d, goldenMAPMaximum(d) is the supremum "
                    + "of positive lengths n for which there exist a zero-indexed starting "
                    + "position i and a Boolean letter a such that goldenWord(i+k d)=a "
                    + "for every k<n. True denotes the paper's letter 0 and false denotes "
                    + "letter 1. For positive d the set has a finite attained maximum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-map-strict-bound"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Strict bound at every positive difference"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The actual word is read at fractional coordinates "
                    + "{(i+k d+1) tau}. For small steps, a monochromatic run cannot wrap "
                    + "across the opposite letter's interval. For large steps, consecutive "
                    + "points of a run occur in alternating clusters, whose two-step "
                    + "displacement limits the length. The irrational quadratic norm of "
                    + "the golden ratio and the integer location of the bound give "
                    + "strictness; the remaining small differences satisfy explicit "
                    + "fractional-window inequalities. The result applies to the attained "
                    + "maximum over all starts and both letters."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("joshi-rust-fibonacci-map-bound"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var d = F.Id("d");
        var maximum = Call("goldenMAPMaximum", d);
        var numerator = new Formula.Binary(maximum, FormulaBinaryOperator.Subtract, F.D(1));
        var bound = new Formula.Relation(
            new Formula.Fraction(numerator, d),
            FormulaRelationOperator.LessThan,
            new Formula.Fraction(Seq(Sqrt, Grp(F.D(5))), Tau));
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"), Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Logic(
                new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, d),
                FormulaLogicOperator.Implies,
                bound)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
