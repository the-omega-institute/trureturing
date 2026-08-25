using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class TargetPairCoverageInformationContrastDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/TargetPairCoverageInformationContrast."
            + "target_pair_coverage_and_information_contrast";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite target identification is a pair-cover condition that positive statistical "
            + "information alone need not satisfy.",
        H("Target-Pair Coverage and Information Contrast"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-pair-coverage-and-information-contrast"),
                DeclarationHandle.Create(Declaration),
                H("Target-pair coverage is not replaced by mutual information"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely indexed models and a finite selected experiment set, "
                            + "target identification is equivalent to covering every unordered "
                            + "target-disagreement pair by one selected experiment's separation "
                            + "set. This is the finite hitting-set form of the cover criterion.")),
                    Paragraph(Text(
                        "The concrete prior is supported on two models with the same target. "
                            + "Reading the nuisance coordinate carries exactly log two nats about "
                            + "the full model and separates those same-target models.")),
                    Paragraph(Text(
                        "A second displayed pair has different targets but the same experiment "
                            + "response. Consequently the target cannot factor through the "
                            + "experiment, despite its positive model information."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(OpenBrace, left, Comma, Sp, right, CloseBrace);

    private static Formula Tuple(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula PairSet(
        Formula readout, Formula experiment, Formula left, Formula right) =>
        Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Apply(Apply(readout, experiment), left), Sp, Neq, Sp,
            Apply(Apply(readout, experiment), right), CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula natural = F.Id("n");
        Formula experimentType = F.Id("E");
        Formula responseType = F.Id("R");
        Formula targetType = F.Id("Y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula modelType = Call("Fin", natural);
        Formula selected = F.Id("A");
        Formula readout = F.Id("r");
        Formula target = F.Id("T");
        Formula left = F.Id("i");
        Formula right = F.Id("j");
        Formula experiment = F.Id("a");
        Formula targetPairs = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Apply(target, left), Sp, Neq, Sp, Apply(target, right), CloseBrace);
        Formula separationUnion = Call(
            "Union",
            Seq(experiment, Sp, InMacro, Sp, selected),
            PairSet(readout, experiment, left, right));

        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula falseFalse = Tuple(falseValue, falseValue);
        Formula falseTrue = Tuple(falseValue, trueValue);
        Formula trueFalse = Tuple(trueValue, falseValue);
        Formula mass = F.Mu;
        Formula nuisance = F.Id("e");
        Formula modelTarget = F.Id("T");
        Formula model = Tuple(F.Id("b"), F.Id("c"));
        Formula boolType = F.Id("Bool");
        Formula boolModelType = Seq(boolType, Sp, Times, Sp, boolType);
        Formula realType = Seq(Mathbb, Grp(F.Id("R")));
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula law = Call("readoutTargetLaw", mass, nuisance, F.Id("id"));
        Formula recovery = F.Id("f");

        return Disp(new Formula.Aligned([
            Seq(
                Open, Forall, Sp, natural, Colon, Sp, F.Id("Nat"), Comma, Sp,
                experimentType, Comma, Sp, responseType, Comma, Sp,
                targetType, Colon, Sp, type, Comma),
            Seq(
                Call("DecidableEq", experimentType), Sp, Rightarrow, Sp,
                Forall, Sp,
                selected, Colon, Sp, Call("Finset", experimentType), Comma),
            Seq(
                readout, Colon, Sp, experimentType, Sp, To, Sp, modelType, Sp, To, Sp,
                responseType, Comma, Sp,
                target, Colon, Sp, modelType, Sp, To, Sp, targetType, Comma),
            Seq(
                Open, Forall, Sp, left, Comma, Sp, right, Colon, Sp, modelType, Comma, Sp,
                Apply(target, left), Sp, Neq, Sp, Apply(target, right), Sp,
                Rightarrow, Sp, Exists, Sp, experiment, Sp, InMacro, Sp, selected, Comma),
            Seq(
                Apply(Apply(readout, experiment), left), Sp, Neq, Sp,
                Apply(Apply(readout, experiment), right), Close, Sp, Iff, Sp),
            Seq(targetPairs, Sp, Subseteq, Sp, separationUnion, Close, Sp, Land, Sp),
            Seq(
                Open, Operatorname, Grp(F.Id("let")), Sp,
                mass, Colon, Sp, boolModelType, Sp, To, Sp, realType,
                Sp, Colon, Eq, Sp, Open, model, Sp, Mapsto, Sp,
                Call("if", Seq(F.Id("b"), Sp, Eq, Sp, falseValue), half, D(0)), Close,
                Comma, Sp),
            Seq(
                nuisance, Colon, Sp, boolModelType, Sp, To, Sp, boolType,
                Sp, Colon, Eq, Sp, Open, model, Sp, Mapsto, Sp,
                F.Id("c"), Close, Comma, Sp),
            Seq(
                modelTarget, Colon, Sp, boolModelType, Sp, To, Sp, boolType,
                Sp, Colon, Eq, Sp, Open, model, Sp, Mapsto, Sp,
                F.Id("b"), Close, SemiSpace),
            Seq(
                Call("mutualInformation", law), Sp, Eq, Sp, Log, Sp, D(2), Sp,
                Land, Sp,
                Apply(nuisance, falseFalse), Sp, Neq, Sp,
                Apply(nuisance, falseTrue), Sp, Land, Sp),
            Seq(
                Apply(modelTarget, falseFalse), Sp, Eq, Sp,
                Apply(modelTarget, falseTrue), Sp, Land, Sp,
                Apply(nuisance, falseFalse), Sp, Eq, Sp,
                Apply(nuisance, trueFalse), Sp, Land, Sp),
            Seq(
                Apply(modelTarget, falseFalse), Sp, Neq, Sp,
                Apply(modelTarget, trueFalse), Sp, Land, Sp,
                Neg, Exists, Sp, recovery, Colon, Sp,
                Seq(F.Id("Bool"), Sp, To, Sp, F.Id("Bool")), Comma, Sp,
                modelTarget, Sp, Eq, Sp, recovery, Sp, Circ, Sp, nuisance,
                Close, Dot),
        ]));
    }
}
