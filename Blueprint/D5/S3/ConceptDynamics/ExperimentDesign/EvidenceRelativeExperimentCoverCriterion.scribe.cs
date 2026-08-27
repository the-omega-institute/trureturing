using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class EvidenceRelativeExperimentCoverCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/EvidenceRelativeExperimentCoverCriterion."
            + "evidence_relative_experiment_cover_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite experiment selection identifies a target exactly by covering the ordered "
            + "pairs unresolved by current evidence.",
        H("Evidence-Relative Experiment Cover Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("evidence-relative-experiment-cover-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Target identification is ordered-pair cover"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The current evidence, dependent experiment readouts, and target are "
                        + "source primitives on one model carrier. The selected experiment "
                        + "interface is the canonical dependent joint readout.")),
                Paragraph(Text(
                    "The left set contains ordered model pairs with equal current evidence "
                        + "and unequal target values. Each selected experiment contributes "
                        + "the members of that same set whose experiment responses differ.")),
                Paragraph(Text(
                    "Target factorization through current evidence paired with the selected "
                        + "joint readout is equivalent to coverage of every unresolved ordered "
                        + "pair. The argument does not require the model carrier itself to be "
                        + "finite."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, clauses[index]);
        }
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula modelType = F.Id("Model");
        Formula experimentType = F.Id("Experiment");
        Formula evidenceType = F.Id("Evidence");
        Formula targetType = F.Id("Target");
        Formula responseFamily = F.Id("Response");
        Formula selected = F.Id("A0");
        Formula baseline = F.Id("E");
        Formula readout = F.Id("Ea");
        Formula target = F.Id("T");
        Formula experiment = F.Id("a");
        Formula model = F.Id("m");
        Formula pair = F.Id("p");
        Formula pairType = Seq(modelType, Sp, Times, Sp, modelType);
        Formula first = Call("fst", pair);
        Formula second = Call("snd", pair);
        Formula selectedReadout = Call("restrict", readout, selected);
        Formula jointAtModel = Call("jointReadout", selectedReadout, model);
        Formula combinedEvidence = Seq(
            Open,
            model,
            Sp,
            Mapsto,
            Sp,
            Open,
            Apply(baseline, model),
            Comma,
            Sp,
            jointAtModel,
            Close,
            Close);
        Formula unresolved = And(
            new Formula.Relation(
                Apply(baseline, first),
                FormulaRelationOperator.Equal,
                Apply(baseline, second)),
            new Formula.Relation(
                Apply(target, first),
                FormulaRelationOperator.NotEqual,
                Apply(target, second)));
        Formula separated = And(
            unresolved,
            new Formula.Relation(
                Apply(Apply(readout, experiment), first),
                FormulaRelationOperator.NotEqual,
                Apply(Apply(readout, experiment), second)));
        Formula unresolvedSet = Seq(
            OpenBrace,
            pair,
            Sp,
            InMacro,
            Sp,
            pairType,
            Sp,
            Mid,
            Sp,
            unresolved,
            CloseBrace);
        Formula separationSet = Seq(
            OpenBrace,
            pair,
            Sp,
            InMacro,
            Sp,
            pairType,
            Sp,
            Mid,
            Sp,
            separated,
            CloseBrace);
        Formula cover = Seq(
            unresolvedSet,
            Sp,
            Subseteq,
            Sp,
            Call("Union", Seq(experiment, Sp, InMacro, Sp, selected), separationSet));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(
                    Seq(modelType, Comma, Sp, experimentType, Comma, Sp,
                        evidenceType, Comma, Sp, targetType),
                    type),
                Comma),
            Seq(
                Typed(responseFamily, Arrow(experimentType, type)),
                Comma,
                Sp,
                Typed(selected, Call("Finset", experimentType)),
                Comma),
            Seq(
                Typed(baseline, Arrow(modelType, evidenceType)),
                Comma,
                Sp,
                readout,
                Colon,
                Sp,
                Forall,
                Sp,
                Typed(experiment, experimentType),
                Comma,
                Sp,
                modelType,
                Sp,
                To,
                Sp,
                Apply(responseFamily, experiment),
                Comma),
            Seq(Typed(target, Arrow(modelType, targetType)), Comma),
            Seq(
                Call("FactorsThrough", target, combinedEvidence),
                Sp,
                Iff,
                Sp),
            Seq(cover, Dot),
        ]));
    }
}
