using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Discussion;

internal sealed class CommonSourceEchoLimitDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Discussion/CommonSourceEchoLimit."
            + "common_source_repetition_cannot_resolve_blind_target";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Messages derived from one common source cannot resolve a target blind to that source.",
        H("Common-Source Echo Limit"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-source-repetition-cannot-resolve-a-blind-target"),
            DeclarationHandle.Create(Declaration),
            H("Common-source repetition cannot resolve a blind target"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take an arbitrary indexed family of messages. If every message factors "
                        + "through the same source readout, their canonical joint readout also "
                        + "factors through that source and cannot determine a target that the "
                        + "source does not determine.")),
                Paragraph(Text(
                    "Consequently, if the joint message readout does determine the target, "
                        + "at least one component message must introduce a distinction that "
                        + "does not factor through the common source."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula sourceType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula messageType = F.Id("BM");
        Formula source = F.Id("S");
        Formula message = F.Id("M");
        Formula target = F.Id("T");
        Formula index = F.Id("i");
        Formula messageAt = Apply(message, index);
        Formula targetReadout = Call("canonicalTargetReadout", target);
        Formula jointMessages = Call("jointReadout", message);
        Formula targetBlind = new Formula.Not(
            Call("Refines", targetReadout, source));
        Formula messageFamilyType = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            indexType,
            Arrow(stateType, Apply(messageType, index)));
        Formula everyMessageBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            indexType,
            Call("Refines", messageAt, source));
        Formula jointTargetResolved = Call(
            "Refines", targetReadout, jointMessages);
        Formula persistence = Implies(
            everyMessageBound,
            new Formula.Not(jointTargetResolved));
        Formula outsideMessage = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("i"),
            indexType,
            new Formula.Not(Call("Refines", messageAt, source)));
        Formula necessity = Implies(jointTargetResolved, outsideMessage);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type),
                Bound("X", type),
                Bound("B", type),
                Bound("Y", type),
                Bound("BM", Arrow(indexType, type)),
                Bound("S", Arrow(stateType, sourceType)),
                Bound("M", messageFamilyType),
                Bound("T", Arrow(stateType, targetType)),
            ],
            Implies(targetBlind, And(persistence, necessity))));
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
