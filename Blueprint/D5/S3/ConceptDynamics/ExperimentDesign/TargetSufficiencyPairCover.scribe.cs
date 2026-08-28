using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class TargetSufficiencyPairCoverDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/TargetSufficiencyPairCover."
            + "target_sufficiency_iff_pair_cover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target sufficiency is exact coverage of target-disagreement pairs.",
        H("Target Sufficiency Pair Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-sufficiency-iff-pair-cover"),
                DeclarationHandle.Create(Declaration),
                H("Target sufficiency is target-pair coverage"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Models are indexed by Fin(n), and J is a finite selection from the "
                            + "ambient experiment type. The selected observations are assembled "
                            + "by the canonical dependent joint readout.")),
                    Paragraph(Text(
                        "The required unordered-pair universe contains exactly the model pairs "
                            + "with unequal target values. Each selected experiment contributes "
                            + "only those required pairs whose responses it separates.")),
                    Paragraph(Text(
                        "The target is constant on joint-readout fibers exactly when those "
                            + "target-relevant separation sets cover the required universe. "
                            + "No baseline observation or full-state injectivity is assumed."))),
                DescribeRole.Theorem))));

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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(OpenBrace, left, Comma, Sp, right, CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula natural = F.Id("Nat");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula n = F.Id("n");
        Formula experimentType = F.Id("Experiment");
        Formula responseFamily = F.Id("Response");
        Formula targetType = F.Id("Target");
        Formula selected = F.Id("J");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula experiment = F.Id("e");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula modelType = Call("Fin", n);
        Formula responseAtExperiment = Apply(responseFamily, experiment);
        Formula selectedReadout = Call("restrict", readout, selected);
        Formula targetUniverse = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Apply(target, left), Sp, Neq, Sp, Apply(target, right), CloseBrace);
        Formula separationSet = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Apply(target, left), Sp, Neq, Sp, Apply(target, right),
            Sp, Land, Sp,
            Apply(Apply(readout, experiment), left), Sp, Neq, Sp,
            Apply(Apply(readout, experiment), right), CloseBrace);
        Formula selectedUnion = Call(
            "Union", Seq(experiment, Sp, InMacro, Sp, selected), separationSet);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(n, natural), Comma, Sp,
                Typed(Seq(experimentType, Comma, Sp, targetType), type), Comma),
            Seq(
                Typed(responseFamily, Arrow(experimentType, type)), Comma, Sp,
                Typed(selected, Call("Finset", experimentType)), Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp,
                Typed(experiment, experimentType), Comma, Sp,
                modelType, Sp, To, Sp, responseAtExperiment, Comma),
            Seq(Typed(target, Arrow(modelType, targetType)), Comma),
            Seq(
                Call("FactorsThrough", target,
                    Call("jointReadout", selectedReadout)), Sp, Iff, Sp),
            Seq(targetUniverse, Sp, Eq, Sp, selectedUnion, Dot),
        ]));
    }
}
