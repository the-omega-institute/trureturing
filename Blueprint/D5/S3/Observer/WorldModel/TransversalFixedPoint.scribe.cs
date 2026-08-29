using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class TransversalFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/TransversalFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coherent family of states across semiconjugate world models forms a transversal fixed point whenever one anchor state is fixed.",
        H("Transversal Fixed Point"),
        Blocks(
            Theorem(
                "transport-from-fixed-is-fixed",
                "transport_from_fixed_is_fixed",
                WorldmodeldiagramTransportFromFixedIsFixedFormula(),
                "Transport From Fixed Is Fixed",
                "A fixed anchor transports to a fixed state in every target world model.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "coherent-section-fixed-from-anchor",
                "coherent_section_fixed_from_anchor",
                WorldmodeldiagramCoherentSectionFixedFromAnchorFormula(),
                "Coherent Section Fixed From Anchor",
                "A coherent section that is fixed at one anchor is fixed in every model.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-at-anchor-iff-fixed-at-target-of-injective",
                "fixed_at_anchor_iff_fixed_at_target_of_injective",
                WorldmodeldiagramFixedAtAnchorIffFixedAtTargetOfInjectiveFormula(),
                "Fixed At Anchor iff Fixed At Target Of Injective",
                "For a coherent section, fixedness at any two anchors is equivalent when the bridge in one direction is injective.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula WorldmodeldiagramTransportFromFixedIsFixedFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type"))), Typed(Seq(F.Id("model")), Seq(F.Id("WorldModelDiagram"), Sp, F.Id("Index"))), Typed(Seq(F.Id("anchor")), Seq(F.Id("Index"))), Typed(Seq(F.Id("state")), Seq(F.Id("model"), Dot, F.Id("State"), Sp, F.Id("anchor")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, Open, F.Id("model"), Dot, F.Id("step"), Sp, F.Id("anchor"), Close, Sp, F.Id("state"))],
        Seq(F.Id("model"), Dot, F.Id("IsFixedSection"), Sp, Open, F.Id("model"), Dot, F.Id("transportFrom"), Sp, F.Id("anchor"), Sp, F.Id("state"), Close));

private static Formula WorldmodeldiagramCoherentSectionFixedFromAnchorFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type"))), Typed(Seq(F.Id("model")), Seq(F.Id("WorldModelDiagram"), Sp, F.Id("Index"))), Typed(Seq(F.Id("state")), Seq(F.Id("model"), Dot, F.Id("Section"))), Typed(Seq(F.Id("anchor")), Seq(F.Id("Index")))],
        [],
        [Seq(F.Id("model"), Dot, F.Id("IsCoherentSection"), Sp, F.Id("state")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, Open, F.Id("model"), Dot, F.Id("step"), Sp, F.Id("anchor"), Close, Sp, Open, F.Id("state"), Sp, F.Id("anchor"), Close)],
        Seq(F.Id("model"), Dot, F.Id("IsFixedSection"), Sp, F.Id("state")));

private static Formula WorldmodeldiagramFixedAtAnchorIffFixedAtTargetOfInjectiveFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type"))), Typed(Seq(F.Id("model")), Seq(F.Id("WorldModelDiagram"), Sp, F.Id("Index"))), Typed(Seq(F.Id("state")), Seq(F.Id("model"), Dot, F.Id("Section"))), Typed(Seq(F.Id("anchor")), Seq(F.Id("Index"))), Typed(Seq(F.Id("target")), Seq(F.Id("Index")))],
        [],
        [Seq(F.Id("model"), Dot, F.Id("IsCoherentSection"), Sp, F.Id("state")), Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, Open, F.Id("model"), Dot, F.Id("bridge"), Sp, F.Id("anchor"), Sp, F.Id("target"), Close)],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, Open, F.Id("model"), Dot, F.Id("step"), Sp, F.Id("anchor"), Close, Sp, Open, F.Id("state"), Sp, F.Id("anchor"), Close, Sp, Leftrightarrow, Sp, F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, Open, F.Id("model"), Dot, F.Id("step"), Sp, F.Id("target"), Close, Sp, Open, F.Id("state"), Sp, F.Id("target"), Close));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
