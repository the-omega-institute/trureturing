using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class OrderedTimeSimplexSecondMagnusAverageDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The triangularly weighted ordered-time response has a closed finite-horizon formula.",
        H("Ordered-Time Simplex Second-Magnus Average"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordered-time-simplex-kernel-average-formula"),
            DeclarationHandle.Create(
                Prefix + "ordered_time_simplex_kernel_average_formula"),
            H("Exact ordered-simplex response"),
            StatementSource.FromAuthor(AverageFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a nonzero frequency gap, collapsing the ordered two-time simplex to "
                        + "the time difference gives a triangularly weighted squared sine "
                        + "integral with an exact closed form.")),
                Paragraph(Text(
                    "The formula supplies a common finite horizon for each fixed gap. A uniform "
                        + "minimum over a finite frequency family and a Bochner-valued Magnus "
                        + "integral remain future transport steps."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula.BoundVariable Bound(FormulaIdentifier name, Formula domain) =>
        new(name, domain);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(value), D(2));

    private static Formula AverageFormula()
    {
        Formula gap = F.Id("g");
        Formula horizon = F.Id("T");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula average = Call(
            FormulaIdentifier.Create("A"), gap, horizon);
        Formula oscillation = Call(
            FormulaIdentifier.Create("cos"),
            Seq(gap, Sp, Times, Sp, horizon));
        Formula correction = Seq(
            Frac,
            Grp(Seq(D(2), Sp, Times, Sp,
                Open, D(1), Sp, Minus, Sp, oscillation, Close)),
            Grp(Square(gap)));
        Formula conclusion = new Formula.Relation(
            average,
            FormulaRelationOperator.Equal,
            Seq(Square(horizon), Sp, Minus, Sp, correction));
        Formula body = Seq(
            gap, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp, conclusion);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound(FormulaIdentifier.Create("g"), real),
                Bound(FormulaIdentifier.Create("T"), real),
            ],
            body));
    }
}
