using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class CollapseIsExpandingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var base13 = Id("betaThirteen");

        var statement = new Formula.Relation(
            Num(1), FormulaRelationOperator.LessThan, new Formula.Absolute(base13));

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/CollapseIsExpanding.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-block collapse is the general expanding-orbit lemma at one multiplier.",
            H("Collapse Is Expanding"),
            Blocks(
                Paragraph(Text(
                    "The escape core of the period-block collapse is a fact about any expanding "
                        + "multiplier, and that fact is stated one tier up, where it may not "
                        + "mention this base at all. What remains here is the instantiation: the "
                        + "signed step, which the earlier module states only under absolute "
                        + "value, and the earlier module's own distance identity reached by the "
                        + "general route. Should either side change, this stops compiling.")),
                Paragraph(Text(
                    "The module exists because the link was first written inside the general "
                        + "one, where the generality ordering forbids it. A rule recorded earlier "
                        + "the same day held that a generalisation owes the specific form an "
                        + "in-place link, preferring that to a separate artifact. Under the "
                        + "ordering the in-place link is not available. The obligation stands; "
                        + "the location was wrong.")),
                Describe.Lean(
                    DescribeId.Create("the-collapse-is-the-general-lemma"),
                    DeclarationHandle.Create(
                        declarationPrefix + "the_collapse_is_the_general_lemma"),
                    H("The collapse is the general lemma"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed half is that the base is expanding, which is what lets the "
                            + "general lemma apply here at all. The second half is the distance "
                            + "identity, re-derived rather than restated."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/PeriodicCollapse")),
            ]));
    }
}
