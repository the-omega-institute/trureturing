using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class TargetRelativePairUniverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target identification requires separating exactly the unordered model pairs on "
            + "which the target values differ.",
        H("Target-Relative Pair Universe"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-relative-pair-universe"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/TargetRelativePairUniverse."
                        + "target_relative_pair_universe"),
                H("Target identifiability is coverage of target-disagreement pairs"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The required universe is constructed canonically on Sym2(Fin n): it "
                            + "contains precisely the unordered pairs of models whose target "
                            + "values differ. Pairs with equal target values impose no "
                            + "identification requirement.")),
                    Paragraph(Text(
                        "Each intervention contributes the unordered pairs separated by its "
                            + "readout. The theorem states that every target-disagreement pair "
                            + "admits such an intervention exactly when the target-relative "
                            + "universe is covered by the union of these separation sets."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(OpenBrace, left, Comma, Sp, right, CloseBrace);

    private static Formula SeparationSet(
        Formula intervention,
        Formula readout,
        Formula left,
        Formula right) =>
        Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Apply(Apply(readout, intervention), left), Sp, Neq, Sp,
            Apply(Apply(readout, intervention), right), CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula interventionType = F.Id("I");
        Formula responseType = F.Id("R");
        Formula targetType = F.Id("Y");
        Formula modelType = Seq(Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close);
        Formula readout = F.Id("r");
        Formula target = F.Id("T");
        Formula intervention = F.Id("a");
        Formula left = F.Id("i");
        Formula right = F.Id("j");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula targetUniverse = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Apply(target, left), Sp, Neq, Sp, Apply(target, right), CloseBrace);
        Formula interventionUnion = Call(
            "Union",
            intervention,
            SeparationSet(intervention, readout, left, right));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, interventionType, Comma, Sp, responseType, Comma, Sp,
                targetType, Colon, Sp, type, Comma),
            Seq(
                readout, Colon, Sp, interventionType, Sp, To, Sp, modelType, Sp, To, Sp,
                responseType, Comma, Sp,
                target, Colon, Sp, modelType, Sp, To, Sp, targetType, Comma),
            Seq(
                Open, Forall, Sp, left, Comma, Sp, right, Colon, Sp, modelType, Comma, Sp,
                Apply(target, left), Sp, Neq, Sp, Apply(target, right), Sp,
                Rightarrow, Sp, Exists, Sp, intervention, Colon, Sp, interventionType,
                Comma, Sp,
                Apply(Apply(readout, intervention), left), Sp, Neq, Sp,
                Apply(Apply(readout, intervention), right), Close),
            Seq(Iff, Sp, targetUniverse, Sp, Subseteq, Sp, interventionUnion, Dot),
        ]));
    }
}
