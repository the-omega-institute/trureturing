using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class FullCirclePrimalAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/FullCirclePrimalAttainment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every feasible budgeted continuous moment problem on the unit circle attains its "
            + "largest dominated normalized-Haar coefficient.",
        H("Full Circle Primal Attainment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-circle-haar-construction"),
                DeclarationHandle.Create(Prefix + "normalizedCircleHaar"),
                H("Normalized Haar measure on the unit circle"),
                StatementSource.FromAuthor(HaarDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The measure is constructed on the exact complex unit circle by pushing "
                        + "the normalized additive-circle Haar probability measure through the "
                        + "canonical homeomorphism."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-circle-haar-unit-mass"),
                DeclarationHandle.Create(Prefix + "normalizedCircleHaar_mass"),
                H("Normalized circle Haar has unit mass"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("mass", HaarSymbol()), Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Measure preservation under the circle homeomorphism carries the unit "
                        + "mass of normalized additive Haar to the complex unit circle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-circle-moment-problem-attains-haar-floor"),
                DeclarationHandle.Create(Prefix + "full_circle_primal_attainment"),
                H("A feasible circle primal attains its maximal Haar floor"),
                StatementSource.FromAuthor(AttainmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The premise displays the budget and every continuous circle-moment "
                            + "constraint. The conclusion returns a feasible measure and an "
                            + "actually dominated normalized-Haar coefficient.")),
                    Paragraph(Text(
                        "The final universal comparison quantifies over every feasible measure "
                            + "and every Haar coefficient it dominates, so the selected "
                            + "coefficient is attained and globally maximal.")),
                    Paragraph(Text(
                        "Compactness is applied to pairs consisting of the Haar coefficient and "
                            + "a residual positive finite measure. Measure subtraction converts "
                            + "any competing domination inequality into such a pair."))),
                DescribeRole.Theorem))));

    private static Formula HaarDefinitionFormula()
    {
        Formula additiveCircle = Call("AddCircle", Seq(D(2), Sp, Cdot, Sp, Pi));
        Formula circleHomeomorphism =
            Seq(Operatorname, Grp(F.Id("homeomorphCircle")), Apos);
        return Disp(Seq(
            HaarSymbol(), Colon, Sp, Call("FiniteMeasure", F.Id("Circle")), Sp,
            Eq, Sp, Call("map", circleHomeomorphism,
                Call("haarAddCircle", additiveCircle)), Dot));
    }

    private static Formula AttainmentFormula()
    {
        Formula indexType = F.Id("iota");
        Formula circle = F.Id("Circle");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nonnegativeReal = Seq(
            Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, D(0)));
        Formula moment = F.Id("Gamma");
        Formula target = F.Id("w");
        Formula budget = F.Id("C");
        Formula measure = Mu;
        Formula competitor = Nu;
        Formula alpha = Alpha;
        Formula beta = Beta;
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula momentType = Seq(
            indexType, Sp, To, Sp, Call("ContinuousMap", circle, real));
        Formula targetType = Seq(indexType, Sp, To, Sp, real);
        Formula feasibleMeasure = Feasible(moment, target, budget, measure, indexType, circle);
        Formula feasibleCompetitor =
            Feasible(moment, target, budget, competitor, indexType, circle);
        Formula haar = HaarSymbol();
        Formula selectedFloor = Seq(alpha, Sp, Cdot, Sp, haar, Sp, Leq, Sp, measure);
        Formula competingFloor = Seq(beta, Sp, Cdot, Sp, haar, Sp, Leq, Sp, competitor);

        return Disp(Seq(
            Forall, Sp, indexType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            moment, Colon, Sp, momentType, Comma, Sp,
            target, Colon, Sp, targetType, Comma, RowBreak, Grp(),
            budget, Colon, Sp, nonnegativeReal, Comma, Sp,
            Open, Exists, Sp, measure, Colon, Sp, finiteMeasure, Comma, Sp,
            feasibleMeasure, Close, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, measure, Colon, Sp, finiteMeasure, Comma, Sp,
            Call("mass", measure), Sp, Leq, Sp, budget, Sp, Land, RowBreak, Grp(),
            Open, MomentConstraints(moment, target, measure, indexType, circle), Close,
            Sp, Land, RowBreak, Grp(),
            Exists, Sp, alpha, Colon, Sp, nonnegativeReal, Comma, Sp,
            selectedFloor, Sp, Land, RowBreak, Grp(),
            Forall, Sp, competitor, Colon, Sp, finiteMeasure, Comma, Sp,
            Call("mass", competitor), Sp, Leq, Sp, budget, Sp, Rightarrow, RowBreak, Grp(),
            Open, MomentConstraints(moment, target, competitor, indexType, circle), Close, Sp,
            Rightarrow, RowBreak, Grp(),
            Forall, Sp, beta, Colon, Sp, nonnegativeReal, Comma, Sp,
            competingFloor, Sp, Rightarrow, Sp, beta, Sp, Leq, Sp, alpha, Dot));
    }

    private static Formula Feasible(
        Formula moment,
        Formula target,
        Formula budget,
        Formula measure,
        Formula indexType,
        Formula circle) =>
        Seq(
            Call("mass", measure), Sp, Leq, Sp, budget, Sp, Land, Sp,
            Open, MomentConstraints(moment, target, measure, indexType, circle), Close);

    private static Formula MomentConstraints(
        Formula moment,
        Formula target,
        Formula measure,
        Formula indexType,
        Formula circle)
    {
        Formula index = F.Id("i");
        Formula point = F.Id("z");
        Formula integrand = Apply(Apply(moment, index), point);
        Formula integral = Seq(
            Int, Underscore, Grp(circle), Sp, integrand, Sp,
            Mathrm, Grp(F.Id("d")), measure);
        return Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            integral, Sp, Eq, Sp, Apply(target, index));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula HaarSymbol() =>
        Seq(F.Id("m"), Underscore, Grp(F.Id("T")));
}
