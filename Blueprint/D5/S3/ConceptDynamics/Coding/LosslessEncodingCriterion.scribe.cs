using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class LosslessEncodingCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An encoding is lossless on a sender exactly when it is injective on the "
            + "coordinates that sender realizes.",
        H("Lossless Encoding Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lossless-encoding-is-injective-on-the-sender-image"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "lossless_iff_injective_on_image"),
                H("Losslessness is injectivity on the sender image"),
                StatementSource.FromAuthor(LosslessCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Only source coordinates that the sender actually realizes matter. The "
                            + "encoder is injective on that image exactly when two states have "
                            + "the same encoded message precisely when they already have the "
                            + "same sender coordinate.")),
                    Paragraph(Text(
                        "Injectivity prevents the encoder from merging distinct realized "
                            + "coordinates. Conversely, equality reflection for every pair of "
                            + "states proves injectivity by choosing witnesses for the two "
                            + "coordinates in the sender image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noninjectivity-is-a-collapsed-sender-distinction"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "not_injective_on_image_iff_strictly_coarser"),
                H("Noninjectivity is exactly a collapsed sender distinction"),
                StatementSource.FromAuthor(StrictlyCoarserFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Failure of injectivity on the realized sender image is equivalent to a "
                        + "pair of states with one message but different sender coordinates. "
                        + "Thus the abstract injectivity failure is exactly a concrete "
                        + "distinction that the encoding erases."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("the-importance-of-a-lost-distinction-depends-on-the-target"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "lost_distinction_importance_depends_on_target"),
                H("The importance of a lost distinction depends on the target"),
                StatementSource.FromAuthor(TargetDependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a lossy encoder, the message remains recoverable from itself by the "
                            + "identity map, so it is still a decidable target of the message "
                            + "readout.")),
                    Paragraph(Text(
                        "The sender's full concept cannot factor through that same message. A "
                            + "factor map would assign equal sender coordinates to the collapsed "
                            + "pair supplied by noninjectivity, contradicting that the pair was "
                            + "a genuine sender distinction."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Message(Formula sender, Formula encoder) =>
        Call("messageConcept", sender, encoder);

    private static Formula MessageAt(
        Formula sender,
        Formula encoder,
        Formula state) =>
        Call("messageConcept", sender, encoder, state);

    private static Formula InjectiveOnSenderImage(Formula sender, Formula encoder) =>
        Call("InjOn", encoder, Call("range", sender));

    private static Formula Refines(Formula target, Formula information) =>
        Call("Refines", target, information);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula.BoundVariable[] EncodingContext(
        Formula state,
        Formula source,
        Formula message,
        Formula sender,
        Formula encoder) =>
        [
            Bound("X", F.Id("Type")),
            Bound("S", F.Id("Type")),
            Bound("M", F.Id("Type")),
            Bound("sender", Arrow(state, source)),
            Bound("encoder", Arrow(source, message)),
        ];

    private static Formula LosslessCriterionFormula()
    {
        Formula state = F.Id("X");
        Formula source = F.Id("S");
        Formula message = F.Id("M");
        Formula sender = F.Id("sender");
        Formula encoder = F.Id("encoder");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula sameFibers = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", state), Bound("y", state)],
            new Formula.Logic(
                Equal(
                    MessageAt(sender, encoder, left),
                    MessageAt(sender, encoder, right)),
                FormulaLogicOperator.Iff,
                Equal(Apply(sender, left), Apply(sender, right))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. EncodingContext(state, source, message, sender, encoder)],
            new Formula.Logic(
                InjectiveOnSenderImage(sender, encoder),
                FormulaLogicOperator.Iff,
                sameFibers)));
    }

    private static Formula StrictlyCoarserFormula()
    {
        Formula state = F.Id("X");
        Formula source = F.Id("S");
        Formula message = F.Id("M");
        Formula sender = F.Id("sender");
        Formula encoder = F.Id("encoder");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula collapsedDistinction = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", state), Bound("y", state)],
            new Formula.Logic(
                Equal(
                    MessageAt(sender, encoder, left),
                    MessageAt(sender, encoder, right)),
                FormulaLogicOperator.And,
                NotEqual(Apply(sender, left), Apply(sender, right))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. EncodingContext(state, source, message, sender, encoder)],
            new Formula.Logic(
                new Formula.Not(InjectiveOnSenderImage(sender, encoder)),
                FormulaLogicOperator.Iff,
                collapsedDistinction)));
    }

    private static Formula TargetDependenceFormula()
    {
        Formula state = F.Id("X");
        Formula source = F.Id("S");
        Formula message = F.Id("M");
        Formula sender = F.Id("sender");
        Formula encoder = F.Id("encoder");
        Formula encodedMessage = Message(sender, encoder);
        Formula consequence = new Formula.Logic(
            Refines(encodedMessage, encodedMessage),
            FormulaLogicOperator.And,
            new Formula.Not(Refines(sender, encodedMessage)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. EncodingContext(state, source, message, sender, encoder)],
            new Formula.Logic(
                new Formula.Not(InjectiveOnSenderImage(sender, encoder)),
                FormulaLogicOperator.Implies,
                consequence)));
    }
}
