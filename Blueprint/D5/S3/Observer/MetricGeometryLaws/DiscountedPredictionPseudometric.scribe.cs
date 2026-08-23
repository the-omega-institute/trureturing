using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class DiscountedPredictionPseudometricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discounted prediction distance is a bounded pseudometric.",
        H("Discounted Prediction Pseudometric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discounted-prediction-distance-is-a-bounded-pseudometric"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric."
                        + "discounted_prediction_pseudometric"),
                H("Discounted prediction distance is a bounded pseudometric"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The output carrier has its canonical pseudometric, and every output "
                            + "distance is bounded by D. A deterministic update and readout are "
                            + "combined with a discount factor gamma in (0, 1].")),
                    Paragraph(Text(
                        "The discounted prediction distance is the supremum of gamma to the "
                            + "time k multiplied by the output distance after k updates. The "
                            + "proof uses the bounded real supremum API and the pseudometric "
                            + "laws pointwise along each orbit.")),
                    Paragraph(Text(
                        "All four source clauses remain public: nonnegativity and the global "
                            + "bound, zero on the diagonal, symmetry, and the triangle "
                            + "inequality."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula gamma = F.Id("gamma");
        Formula bound = F.Id("D");
        Formula y = F.Id("y");
        Formula yPrime = Seq(F.Id("y"), Apos);
        Formula yDoublePrime = Seq(F.Id("y"), Apos, Apos);
        Formula family = Apply("BoundedOutputPseudometric", F.Id("q"), bound);
        Formula discount = Seq(D(0), Lt, Sp, gamma, Sp, Leq, Sp, D(1));
        Formula distance = Apply("DiscountedDistance", y, yPrime);
        Formula diagonal = Apply("DiscountedDistance", y, y);
        Formula symmetry = Seq(
            distance, Sp, Eq, Sp, Apply("DiscountedDistance", yPrime, y));
        Formula triangle = Seq(
            distance, Sp, Leq, Sp,
            Apply("DiscountedDistance", y, yDoublePrime), Sp, Plus, Sp,
            Apply("DiscountedDistance", yDoublePrime, yPrime));
        Formula clauses = Seq(
            Grp(D(0), Leq, Sp, distance, Sp, Leq, Sp, bound), Sp, Land, RowBreak,
            diagonal, Sp, Eq, Sp, D(0), Sp, Land, RowBreak,
            symmetry, Sp, Land, RowBreak,
            triangle);
        return Disp(Seq(
            family, Sp, Land, Sp, discount, Sp, Rightarrow, RowBreak,
            Forall, Sp, y, Comma, Sp, yPrime, Comma, Sp, yDoublePrime,
            InMacro, Sp, F.Id("Y"), Comma, Esc, clauses, Dot));
    }
}
