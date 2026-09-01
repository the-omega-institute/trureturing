using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PairCalibratedSecondMagnusObservabilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair-adapted samples recover four times the finite holonomy energy.",
        H("Pair-Calibrated Second-Magnus Observability"),
        Blocks(Describe.Lean(
            DescribeId.Create("pair-calibrated-second-magnus-energy-equals-four-holonomy"),
            DeclarationHandle.Create(
                Prefix + "pair_calibrated_second_magnus_energy_eq_four_holonomy"),
            H("Exact calibrated reverse observability"),
            StatementSource.FromAuthor(CalibratedEnergyFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For injective frequencies and a curvature field with zero diagonal, each "
                        + "ordered pair is sampled at its own half-turn time separation.")),
                Paragraph(Text(
                    "The resulting calibrated second-Magnus energy is exactly four times the "
                        + "finite holonomy energy. The clocks remain pair dependent, so a "
                        + "family-wide common-window frame bound is still separate."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy")),
        ]));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula CalibratedEnergyFormula()
    {
        Formula frequency = F.Id("omega");
        Formula curvature = F.Id("C");
        Formula p = F.Id("p");
        Formula injective = Call(FormulaIdentifier.Create("Injective"), frequency);
        Formula diagonalZero = Seq(
            Forall, Sp, p, Comma, Sp,
            Apply(curvature, p, p), Sp, Eq, Sp, D(0));
        Formula premises = Seq(
            Open, injective, Sp, Land, Sp, diagonalZero, Close);
        Formula calibratedEnergy = Call(
            FormulaIdentifier.Create("Ecal"), frequency, curvature);
        Formula holonomyEnergy = Call(
            FormulaIdentifier.Create("Ehol"), curvature);
        Formula conclusion = new Formula.Relation(
            calibratedEnergy,
            FormulaRelationOperator.Equal,
            Seq(D(4), Sp, Times, Sp, holonomyEnergy));

        return Disp(Seq(
            premises, Sp, Rightarrow, Sp, conclusion));
    }
}
