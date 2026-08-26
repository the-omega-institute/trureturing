using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionsExchange;

internal sealed class HarmedProbabilityBoundsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionsExchange/HarmedProbabilityBounds."
            + "harmed_probability_frechet_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The harmed potential-outcome probability has the sharp marginal bounds.",
        H("Harmed Probability Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("harmed-potential-outcome-probability-bounds"),
            DeclarationHandle.Create(Declaration),
            H("The harmed probability lies between both marginal bounds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A probability measure on the pair of Boolean potential outcomes "
                        + "supplies the two marginal event probabilities and the joint "
                        + "event in which the first outcome is true while the second is "
                        + "false.")),
                Paragraph(Text(
                    "The joint harmed event is contained in the first marginal and in "
                        + "the complement of the second. The first marginal is contained "
                        + "in the union of the harmed event and the second marginal, "
                        + "which gives the lower bound."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Probability(Formula eventFormula) =>
        Seq(Mu, Open, eventFormula, Close);

    private static Formula TheoremFormula()
    {
        Formula measure = Mu;
        Formula pairBool = Seq(Operatorname, Grp(F.Id("Bool")), Sp, Times, Sp,
            Operatorname, Grp(F.Id("Bool")));
        Formula measureType = Apply("Measure", pairBool);
        Formula probabilityInstance = Apply("IsProbabilityMeasure", measure);
        Formula y0 = F.Id("Y0");
        Formula y1 = F.Id("Y1");
        Formula first = Seq(y0, Sp, Eq, Sp, D(1));
        Formula second = Seq(y1, Sp, Eq, Sp, D(1));
        Formula harmed = Seq(first, Sp, Land, Sp, y1, Sp, Eq, Sp, D(0));
        Formula p0 = Probability(first);
        Formula p1 = Probability(second);
        Formula h = Probability(harmed);
        Formula lower = Seq(Apply("max", D(0), Seq(p0, Sp, Minus, Sp, p1)),
            Sp, Leq, Sp, h);
        Formula upper = Seq(h, Sp, Leq, Sp,
            Apply("min", p0, Seq(D(1), Sp, Minus, Sp, p1)));

        return Disp(Seq(
            Forall, Sp, measure, Colon, Sp, measureType, Comma, Sp,
            OpenBracket, probabilityInstance, CloseBracket, Sp, Rightarrow, Sp,
            Open, lower, Sp, Land, Sp, upper, Close, Dot));
    }
}
