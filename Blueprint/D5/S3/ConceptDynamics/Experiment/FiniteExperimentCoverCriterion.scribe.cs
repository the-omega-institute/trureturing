using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class FiniteExperimentCoverCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion."
            + "finite_experiment_cover_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite experiment package identifies a target relative to current evidence "
            + "exactly when it covers every unresolved target pair.",
        H("Finite Experiment Cover Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-experiment-cover-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Finite experiment design is target-pair set cover"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Models are indexed by Fin n. The current evidence E0 is paired with the "
                        + "canonical joint readout of the finite selected experiment set A; "
                        + "target identifiability is fiber constancy of that combined evidence.")),
                Paragraph(Text(
                    "The unresolved universe contains exactly the unordered model pairs with "
                        + "equal current evidence and unequal target values. Each selected "
                        + "experiment contributes the unresolved pairs whose responses differ.")),
                Paragraph(Text(
                    "The selected package identifies the target exactly when the unresolved "
                        + "universe equals the union of those separation sets. Finite model "
                        + "indexing and the finite selection are sufficient; the ambient "
                        + "experiment type need not itself be finite."))),
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
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula budget = F.Id("n");
        Formula experimentType = F.Id("E");
        Formula evidenceType = F.Id("C");
        Formula targetType = F.Id("Y");
        Formula responseFamily = F.Id("R");
        Formula selected = F.Id("A");
        Formula baseline = F.Id("E0");
        Formula readout = F.Id("Q");
        Formula target = F.Id("T");
        Formula experiment = F.Id("e");
        Formula left = F.Id("i");
        Formula right = F.Id("j");
        Formula modelType = Call("Fin", budget);
        Formula responseAtExperiment = Apply(responseFamily, experiment);
        Formula selectedReadout = Call("restrict", readout, selected);
        Formula leftJoint = Call("jointReadout", selectedReadout, left);
        Formula rightJoint = Call("jointReadout", selectedReadout, right);
        Formula leftEvidence = Seq(
            Open, Apply(baseline, left), Comma, Sp, leftJoint, Close);
        Formula rightEvidence = Seq(
            Open, Apply(baseline, right), Comma, Sp, rightJoint, Close);
        Formula identifies = Seq(
            Forall, Sp, Typed(left, modelType), Comma, Sp,
            Typed(right, modelType), Comma, Sp,
            leftEvidence, Sp, Eq, Sp, rightEvidence, Sp, Rightarrow, Sp,
            Apply(target, left), Sp, Eq, Sp, Apply(target, right));
        Formula unresolvedCondition = Seq(
            Apply(baseline, left), Sp, Eq, Sp, Apply(baseline, right), Sp,
            Land, Sp,
            Apply(target, left), Sp, Neq, Sp, Apply(target, right));
        Formula unresolvedPairs = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            unresolvedCondition, CloseBrace);
        Formula separationSet = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            unresolvedCondition, Sp, Land, Sp,
            Apply(Apply(readout, experiment), left), Sp, Neq, Sp,
            Apply(Apply(readout, experiment), right), CloseBrace);
        Formula selectedUnion = Call(
            "Union", Seq(experiment, Sp, InMacro, Sp, selected), separationSet);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(budget, natural), Comma, Sp,
                Typed(Seq(experimentType, Comma, Sp, evidenceType, Comma, Sp,
                    targetType), type), Comma),
            Seq(
                Typed(responseFamily, Arrow(experimentType, type)), Comma, Sp,
                Typed(selected, Call("Finset", experimentType)), Comma),
            Seq(
                Typed(baseline, Arrow(modelType, evidenceType)), Comma, Sp,
                readout, Colon, Sp, Forall, Sp,
                Typed(experiment, experimentType), Comma, Sp,
                modelType, Sp, To, Sp, responseAtExperiment, Comma),
            Seq(Typed(target, Arrow(modelType, targetType)), Comma),
            Seq(Open, identifies, Close, Sp, Iff, Sp),
            Seq(unresolvedPairs, Sp, Eq, Sp, selectedUnion, Dot),
        ]));
    }
}
