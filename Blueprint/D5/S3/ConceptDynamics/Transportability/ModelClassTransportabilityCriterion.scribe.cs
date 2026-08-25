using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transportability;

internal sealed class ModelClassTransportabilityCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Model-class transportability is exactly absence of a target residual.",
        H("Model-Class Transportability Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("model-class-transportability-criterion"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Transportability/ModelClassTransportabilityCriterion."
                    + "model_class_transportability_criterion"),
            H("Transportability is equivalent to residual emptiness and kernel inclusion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The evidence map records all available source experiments together with "
                        + "the target observational law. The target map records the target "
                        + "effect on the same model class.")),
                Paragraph(Text(
                    "TransRes is rendered by the repository's canonical defectRelation: its "
                        + "elements are precisely model pairs with equal evidence and unequal "
                        + "target values. No parallel residual definition is introduced.")),
                Paragraph(Text(
                    "Restricting both outputs to their realized images makes the computing map "
                        + "canonical and unique, including for an empty model class. The imported "
                        + "effective-image criterion supplies uniqueness and the kernel clause."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("Model");
        Formula evidenceType = F.Id("Evidence");
        Formula targetType = F.Id("Target");
        Formula evidence = F.Id("E");
        Formula target = F.Id("T");
        Formula compute = Phi;
        Formula state = F.Id("M");
        Formula evidenceRange = Call("range", evidence);
        Formula targetRange = Call("range", target);
        Formula evidenceValue = Call("rangeFactorization", evidence, state);
        Formula targetValue = Call("rangeFactorization", target, state);
        Formula uniqueCalculation = Seq(
            Exists, Bang, Sp, compute, Colon, Sp,
            Arrow(evidenceRange, targetRange), Comma, Sp,
            Forall, Sp, state, Colon, Sp, model, Comma, Sp,
            compute, Open, evidenceValue, Close, Sp, Eq, Sp, targetValue);
        Formula residual = Call("TransRes", evidence, target);
        Formula residualEmpty = Seq(residual, Sp, Eq, Sp, Emptyset);
        Formula kernelInclusion = Seq(
            Call("ker", evidence), Sp, Subseteq, Sp, Call("ker", target));

        return Disp(Seq(
            Forall, Sp, model, Comma, Sp, evidenceType, Comma, Sp, targetType,
            Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            evidence, Colon, Sp, Arrow(model, evidenceType), Comma, Sp,
            target, Colon, Sp, Arrow(model, targetType), Comma, RowBreak, Grp(),
            Open, Open, uniqueCalculation, Close, Sp,
            Leftrightarrow, Sp, residualEmpty, Close,
            Sp, Land, RowBreak, Grp(),
            Open, residualEmpty, Sp, Leftrightarrow, Sp, kernelInclusion, Close, Dot));
    }
}
