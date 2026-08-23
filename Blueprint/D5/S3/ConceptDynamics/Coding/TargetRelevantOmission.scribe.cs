using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class TargetRelevantOmissionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target-relevant omission is exactly a collapsed message distinction that matters "
            + "to the target.",
        H("Target-Relevant Omission"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-relevant-omission-has-a-collapsed-distinction-witness"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/TargetRelevantOmission."
                        + "omission_iff_witness_exists"),
                H("Target-relevant omission has a collapsed distinction witness"),
                StatementSource.FromAuthor(OmissionWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonempty state space, assume the sender determines the target. "
                            + "The encoding has a target-relevant omission exactly when two "
                            + "states produce the same message while having different target "
                            + "values and different sender coordinates.")),
                    Paragraph(Text(
                        "In the forward direction, failure to recover the target from the "
                            + "message yields a message fiber on which the target varies. Since "
                            + "the target factors through the sender, that pair must also differ "
                            + "at the sender. Conversely, such a pair rules out every recovery "
                            + "map from messages to target values."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula MessageAt(
        Formula sender,
        Formula encoder,
        Formula state) =>
        Call("messageConcept", sender, encoder, state);

    private static Formula Refines(Formula target, Formula information) =>
        Call("Refines", target, information);

    private static Formula Omission(
        Formula sender,
        Formula encoder,
        Formula target) =>
        Call("TargetRelevantOmission", sender, encoder, target);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula OmissionWitnessFormula()
    {
        Formula state = F.Id("X");
        Formula source = F.Id("S");
        Formula message = F.Id("M");
        Formula targetCarrier = F.Id("Target");
        Formula sender = F.Id("sender");
        Formula encoder = F.Id("encoder");
        Formula target = F.Id("target");
        Formula left = F.Id("x");
        Formula right = F.Id("y");

        Formula assumptions = new Formula.Logic(
            Call("Nonempty", state),
            FormulaLogicOperator.And,
            Refines(target, sender));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", state), Bound("y", state)],
            new Formula.Logic(
                Equal(
                    MessageAt(sender, encoder, left),
                    MessageAt(sender, encoder, right)),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    NotEqual(Apply(target, left), Apply(target, right)),
                    FormulaLogicOperator.And,
                    NotEqual(Apply(sender, left), Apply(sender, right)))));
        Formula characterization = new Formula.Logic(
            Omission(sender, encoder, target),
            FormulaLogicOperator.Iff,
            witness);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("S", F.Id("Type")),
                Bound("M", F.Id("Type")),
                Bound("Target", F.Id("Type")),
                Bound("sender", Arrow(state, source)),
                Bound("encoder", Arrow(source, message)),
                Bound("target", Arrow(state, targetCarrier)),
            ],
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                characterization)));
    }
}
