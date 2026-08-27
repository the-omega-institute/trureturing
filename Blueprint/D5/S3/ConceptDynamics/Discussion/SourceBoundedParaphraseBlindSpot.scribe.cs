using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Discussion;

internal sealed class SourceBoundedParaphraseBlindSpotDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Discussion/SourceBoundedParaphraseBlindSpot."
            + "source_bounded_paraphrases_preserve_target_blind_spot";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Any indexed family of paraphrases bounded by a common source preserves that "
            + "source's target blind spot.",
        H("Source-Bounded Paraphrases Preserve Target Blind Spots"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-bounded-paraphrases-preserve-a-target-blind-spot"),
            DeclarationHandle.Create(Declaration),
            H("Source-bounded paraphrases preserve a target blind spot"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source, target, and dependent indexed family of paraphrase readouts "
                        + "are arbitrary. The public premises say that the source cannot decide "
                        + "the target and that every paraphrase factors through the source.")),
                Paragraph(Text(
                    "The canonical joint readout of the entire paraphrase family still factors "
                        + "through the source. If it decided the target, refinement transitivity "
                        + "would make the target decidable from the source, contradicting the "
                        + "initial blind spot."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula sourceType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula messageType = F.Id("M");
        Formula index = F.Id("i");
        Formula paraphrase = F.Id("p");
        Formula source = F.Id("S");
        Formula target = F.Id("T");
        Formula messageFamilyType = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            indexType,
            Arrow(stateType, Apply(messageType, index)));
        Formula targetReadout = Call("canonicalTargetReadout", target);
        Formula sourceBlindSpot = new Formula.Not(
            Call("Refines", targetReadout, source));
        Formula everyParaphraseBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            indexType,
            Call("Refines", Apply(paraphrase, index), source));
        Formula jointBlindSpot = new Formula.Not(Call(
            "Refines", targetReadout, Call("jointReadout", paraphrase)));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type),
                Bound("X", type),
                Bound("M", Arrow(indexType, type)),
                Bound("B", type),
                Bound("Y", type),
                Bound("p", messageFamilyType),
                Bound("S", Arrow(stateType, sourceType)),
                Bound("T", Arrow(stateType, targetType)),
            ],
            Implies(And(sourceBlindSpot, everyParaphraseBound), jointBlindSpot)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
}
