using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class FiniteFrequencyOrderedSimplexCoercivityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/FiniteFrequencyOrderedSimplexCoercivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nonresonant frequency family has a uniform ordered-simplex energy bound.",
        H("Finite-Frequency Ordered-Simplex Coercivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-ordered-simplex-energy-lower-bound"),
                DeclarationHandle.Create(
                    Prefix + "finite_ordered_simplex_energy_lower_bound"),
                H("Finite-family lower coercivity"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A positive minimum gap gives one common lower response bound for every "
                            + "member of a finite frequency family.")),
                    Paragraph(Text(
                        "The result is finite and analytic; it does not construct a Weil test or "
                            + "supply a zero-side or Robin estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-ordered-simplex-energy-upper-bound"),
                DeclarationHandle.Create(
                    Prefix + "finite_ordered_simplex_energy_upper_bound"),
                H("Finite-family upper envelope"),
                StatementSource.FromAuthor(UpperFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same finite family has the horizon-squared upper envelope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-simplex-coercivity-constant-positive"),
                DeclarationHandle.Create(
                    Prefix + "ordered_simplex_coercivity_constant_pos"),
                H("Positive common-window constant"),
                StatementSource.FromAuthor(PositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A horizon beyond the worst half-turn scale makes the lower constant "
                        + "strictly positive."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage")),
        ]));

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula BoundFormula()
    {
        Formula delta = F.Id("delta");
        Formula gap = F.Id("omega");
        Formula coefficient = F.Id("coefficient");
        Formula horizon = F.Id("horizon");
        Formula minimumGap = Call(FormulaIdentifier.Create("gapFloor"), delta, gap);
        Formula response = Call(FormulaIdentifier.Create("Esimp"), gap, coefficient, horizon);
        Formula coefficientEnergy = F.Id("coefficientEnergy");
        Formula lower = Seq(Open, Square(horizon), Sp, Minus, Sp,
            Frac, D(4), Sp, Slash, Sp, Square(delta), Close,
            Sp, Times, Sp, coefficientEnergy);
        Formula upper = Seq(Square(horizon), Sp, Times, Sp, coefficientEnergy);
        Formula conclusion = Seq(lower, Sp, Leq, Sp, response, Sp, Leq, Sp, upper);
        return Disp(Seq(
            D(0), Sp, Lt, Sp, delta, Sp, Land, Sp, minimumGap, Sp,
            Rightarrow, Sp, conclusion));
    }

    private static Formula UpperFormula() =>
        Disp(Seq(
            Call(FormulaIdentifier.Create("Esimp"), F.Id("omega"),
                F.Id("coefficient"), F.Id("horizon")), Sp, Leq, Sp,
            F.Id("horizon"), Caret, Grp(D(2)), Sp, Times, Sp,
            F.Id("coefficientEnergy")));

    private static Formula PositiveFormula() =>
        Disp(Seq(
            D(2), Sp, Slash, Sp, F.Id("delta"), Sp, Lt, Sp,
            F.Id("horizon"), Rightarrow, Sp,
            D(0), Sp, Lt, Sp,
            F.Id("horizon"), Caret, Grp(D(2)), Sp, Minus, Sp,
            D(4), Sp, Slash, Sp, F.Id("delta"), Caret, Grp(D(2))));

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(value), D(2));
}
