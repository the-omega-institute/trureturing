using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class DescriptiveNormativeSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One descriptive structure admits incompatible normative extensions.",
        H("Descriptive and Normative Structure Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("descriptive-structure-does-not-uniquely-determine-norms"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/DescriptiveNormativeSeparation."
                        + "descriptive_structure_does_not_uniquely_determine_norms"),
                H("Descriptive structure does not uniquely determine norms"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The descriptive record contains the state carrier, physical-admissibility "
                            + "predicate, state-action process, concept readout, and anchored state. "
                            + "A normative extension independently adds a permission predicate on "
                            + "state-action pairs.")),
                    Paragraph(Text(
                        "The first constructed model permits every state-action pair; the second "
                            + "permits none. Both carry exactly the supplied descriptive record, but "
                            + "their permission predicates differ at the public anchor and action "
                            + "witness.")),
                    Paragraph(Text(
                        "Consequently no single function of that shared descriptive record can equal "
                            + "both normative predicates. All model-separation clauses and the explicit "
                            + "failure of unique descriptive inference occur in the public theorem.")),
                    Paragraph(Text(
                        "The source proof itself uses the all-true and all-false predicates, so the "
                            + "formal nontriviality is their genuine normative distinction rather than "
                            + "an invented requirement that each predicate be nonconstant.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact theorem or canonical "
                            + "normative-extension carrier packaging this construction."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula states = F.Id("State");
        Formula actions = F.Id("Action");
        Formula description = F.Id("Description");
        Formula descriptive = F.Id("descriptive");
        Formula actionWitness = F.Id("action");
        Formula firstModel = Subscript(F.Id("M"), D(1));
        Formula secondModel = Subscript(F.Id("M"), D(2));
        Formula firstPermitted = Call("Permitted", firstModel);
        Formula secondPermitted = Call("Permitted", secondModel);
        Formula state = F.Id("x");
        Formula action = F.Id("u");
        Formula infer = F.Id("I");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula descriptiveType = Call("DescriptiveStructure", states, actions, description);
        Formula normativeType = Call("NormativeExtension", states, actions, description);
        Formula sameFirst = Seq(
            Call("Desc", firstModel), Sp, Eq, Sp, descriptive);
        Formula sameSecond = Seq(
            Call("Desc", secondModel), Sp, Eq, Sp, descriptive);
        Formula allPermitted = Seq(
            Open,
            Forall, Sp, state, Colon, Sp, states, Comma, Sp,
            action, Colon, Sp, actions, Comma, Sp,
            Apply(Apply(firstPermitted, state), action), Close);
        Formula nonePermitted = Seq(
            Open,
            Forall, Sp, state, Colon, Sp, states, Comma, Sp,
            action, Colon, Sp, actions, Comma, Sp,
            Neg, Sp, Apply(Apply(secondPermitted, state), action), Close);
        Formula inferenceType = new Formula.TypeArrow(
            descriptiveType,
            new Formula.TypeArrow(states, new Formula.TypeArrow(actions, prop)));
        Formula noSingleInference = Seq(
            Forall, Sp, infer, Colon, Sp, inferenceType, Comma, Sp, Neg, Sp, Open,
            Apply(infer, descriptive), Sp, Eq, Sp, firstPermitted, Sp, Land, Sp,
            Apply(infer, descriptive), Sp, Eq, Sp, secondPermitted, Close);

        return Disp(Seq(
            Forall, Sp, states, Comma, Sp, actions, Comma, Sp, description,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            descriptive, Colon, Sp, descriptiveType, Comma, Sp,
            actionWitness, Colon, Sp, actions, Comma, RowBreak, Grp(),
            Exists, Sp, firstModel, Comma, Sp, secondModel, Colon, Sp, normativeType,
            Comma, RowBreak, Grp(),
            sameFirst, Sp, Land, Sp, sameSecond, Sp, Land, RowBreak, Grp(),
            allPermitted, Sp, Land, RowBreak, Grp(),
            nonePermitted, Sp, Land, RowBreak, Grp(),
            firstPermitted, Sp, Neq, Sp, secondPermitted, Sp, Land,
            RowBreak, Grp(), noSingleInference, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
