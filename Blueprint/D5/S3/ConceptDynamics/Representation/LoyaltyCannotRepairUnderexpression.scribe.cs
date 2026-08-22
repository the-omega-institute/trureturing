using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class LoyaltyCannotRepairUnderexpressionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mandate-loyal representation can remain pointwise insufficient when the mandate "
            + "collapses states with different targets.",
        H("Loyalty Cannot Repair Underexpression"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("loyal-representation-fails-under-collision"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "loyal_representation_fails_under_collision"),
                H("A mandate collision defeats every loyal representation"),
                StatementSource.FromAuthor(CollisionObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A representation is loyal when it factors through the mandate map. "
                            + "It is therefore constant on every mandate fiber, regardless of "
                            + "which factor map is chosen.")),
                    Paragraph(Text(
                        "If two states share a mandate value but have different target values, "
                            + "no loyal representation can agree with the target at both states. "
                            + "Thus a single underexpressed fiber rules out pointwise sufficiency "
                            + "on the whole state space."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("loyalty-cannot-repair-underexpression"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "loyalty_cannot_repair_underexpression"),
                H("Loyalty does not imply target sufficiency"),
                StatementSource.FromAuthor(SeparationWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take Boolean states and let the mandate forget the state completely by "
                            + "mapping both values to the unique element of Unit. Let the target "
                            + "be the Boolean identity and let the representation be constantly "
                            + "false.")),
                    Paragraph(Text(
                        "The constant representation factors through the one-point mandate, so it "
                            + "is fully loyal. Yet true and false lie in the same mandate fiber "
                            + "while the target distinguishes them, and the representation misses "
                            + "the target at true. This concrete witness separates loyalty from "
                            + "sufficiency."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Loyal(Formula mandate, Formula representation) =>
        Call("RepresentationLoyal", mandate, representation);

    private static Formula Sufficient(Formula representation, Formula target) =>
        Call("RepresentationSufficient", representation, target);

    private static Formula Collision(
        Formula stateType,
        Formula mandate,
        Formula target)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", stateType), Bound("y", stateType)],
            And(
                Equal(Apply(mandate, x), Apply(mandate, y)),
                NotEqual(Apply(target, x), Apply(target, y))));
    }

    private static Formula CollisionObstructionFormula()
    {
        Formula stateType = F.Id("X");
        Formula mandateType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula mandate = F.Id("M");
        Formula target = F.Id("T");
        Formula representation = F.Id("J");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("B", F.Id("Type")),
                Bound("Y", F.Id("Type")),
                Bound("M", Arrow(stateType, mandateType)),
                Bound("T", Arrow(stateType, targetType)),
                Bound("J", Arrow(stateType, targetType)),
            ],
            ImpliesFormula(
                Loyal(mandate, representation),
                ImpliesFormula(
                    Collision(stateType, mandate, target),
                    new Formula.Not(Sufficient(representation, target))))));
    }

    private static Formula SeparationWitnessFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula mandate = F.Id("M");
        Formula target = F.Id("T");
        Formula representation = F.Id("J");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("M", Arrow(boolean, unit)),
                Bound("T", Arrow(boolean, boolean)),
                Bound("J", Arrow(boolean, boolean)),
            ],
            And(
                Loyal(mandate, representation),
                And(
                    Collision(boolean, mandate, target),
                    new Formula.Not(Sufficient(representation, target))))));
    }
}
