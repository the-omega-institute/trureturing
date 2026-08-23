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

    private static Formula Named(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula states = F.Id("X");
        Formula actions = F.Id("U");
        Formula description = F.Id("D");
        Formula physical = Subscript(F.Id("Adm"), F.Id("phys"));
        Formula process = F.Id("F");
        Formula concept = F.Id("C");
        Formula anchor = F.Id("a");
        Formula firstModel = Subscript(F.Id("M"), D(1));
        Formula secondModel = Subscript(F.Id("M"), D(2));
        Formula firstPermitted = Subscript(F.Id("P"), D(1));
        Formula secondPermitted = Subscript(F.Id("P"), D(2));
        Formula state = F.Id("x");
        Formula action = F.Id("u");
        Formula infer = F.Id("I");
        Formula descriptiveTuple = Seq(
            Open, states, Comma, Sp, physical, Comma, Sp, process, Comma, Sp,
            concept, Comma, Sp, anchor, Close);
        Formula sameFirst = Seq(
            Named("Desc", firstModel), Sp, Eq, Sp, description);
        Formula sameSecond = Seq(
            Named("Desc", secondModel), Sp, Eq, Sp, description);
        Formula allPermitted = Seq(
            Open,
            Forall, Sp, state, Comma, Sp, action, Comma, Sp,
            Apply(Apply(firstPermitted, state), action), Close);
        Formula nonePermitted = Seq(
            Open,
            Forall, Sp, state, Comma, Sp, action, Comma, Sp,
            Neg, Sp, Apply(Apply(secondPermitted, state), action), Close);
        Formula noSingleInference = Seq(
            Forall, Sp, infer, Comma, Sp, Neg, Sp, Open,
            Apply(infer, description), Sp, Eq, Sp, firstPermitted, Sp, Land, Sp,
            Apply(infer, description), Sp, Eq, Sp, secondPermitted, Close);

        return Disp(Seq(
            description, Sp, Eq, Sp, descriptiveTuple, Comma, Sp,
            actions, Sp, Neq, Sp, Emptyset, Comma, RowBreak, Grp(),
            Exists, Sp, firstModel, Comma, Sp, secondModel, Comma, RowBreak, Grp(),
            firstPermitted, Sp, Eq, Sp, Named("Permitted", firstModel), Comma, Sp,
            secondPermitted, Sp, Eq, Sp, Named("Permitted", secondModel), Comma,
            RowBreak, Grp(),
            sameFirst, Sp, Land, Sp, sameSecond, Sp, Land, RowBreak, Grp(),
            allPermitted, Sp, Land, RowBreak, Grp(),
            nonePermitted, Sp, Land, RowBreak, Grp(),
            firstPermitted, Sp, Neq, Sp, secondPermitted, Sp, Land,
            RowBreak, Grp(), noSingleInference, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
