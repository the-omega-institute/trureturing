using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class InterventionImageDefectDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InterventionLaws/InterventionImageDefect."
            + "image_defect_excludes_joint_model";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A family of intervention laws outside a model class's realizable image "
            + "cannot be explained by one model across every regime.",
        H("Intervention Image Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("image-defect-excludes-joint-model"),
                DeclarationHandle.Create(Declaration),
                H("Image defect excludes a joint explaining model"),
                StatementSource.FromAuthor(ImageDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The model class is a subset of an ambient model carrier. Each model "
                            + "is sent to its complete family of laws indexed by intervention "
                            + "regimes.")),
                    Paragraph(Text(
                        "Image defect says that the observed family is not one of those "
                            + "restricted intervention profiles. A model explaining every "
                            + "regime would construct exactly such a profile, contradicting "
                            + "the defect."))),
                DescribeRole.Theorem))));

    private static Formula ImageDefectFormula()
    {
        Formula modelType = F.Id("Model");
        Formula regimeType = F.Id("Regime");
        Formula lawType = F.Id("Law");
        Formula type = Call("Type");
        Formula modelClass = F.Id("modelClass");
        Formula interventionLaw = F.Id("interventionLaw");
        Formula observedLaw = F.Id("observedLaw");
        Formula model = F.Id("model");
        Formula regime = F.Id("regime");

        Formula pointLaw = Apply(interventionLaw, model, regime);
        Formula profile = Seq(
            Open, LambdaLower, Sp, regime, Comma, Sp, pointLaw, Close);
        Formula realizableProfiles = new Formula.SetBuilder(
            profile,
            model,
            modelClass);
        Formula imageDefect = new Formula.Not(Relation(
            observedLaw,
            FormulaRelationOperator.MemberOf,
            realizableProfiles));

        Formula explainsEveryRegime = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("regime"),
            regimeType,
            Equal(pointLaw, Apply(observedLaw, regime)));
        Formula explainingModel = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("model"),
            modelType,
            And(
                Relation(model, FormulaRelationOperator.MemberOf, modelClass),
                explainsEveryRegime));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Model", type),
                Bound("Regime", type),
                Bound("Law", type),
                Bound("modelClass", Call("Set", modelType)),
                Bound(
                    "interventionLaw",
                    new Formula.TypeArrow(
                        modelType,
                        new Formula.TypeArrow(regimeType, lawType))),
                Bound("observedLaw", new Formula.TypeArrow(regimeType, lawType)),
            ],
            Implies(imageDefect, new Formula.Not(explainingModel))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) => new Formula.Relation(left, relation, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
