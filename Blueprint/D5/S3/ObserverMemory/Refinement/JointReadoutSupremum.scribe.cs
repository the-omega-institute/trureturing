using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class JointReadoutSupremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/Refinement/JointReadoutSupremum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A paired readout has the intersection kernel and is the least common refinement of its two coordinates.",
        H("Joint Readout Supremum"),
        Blocks(
            Theorem(
                "pair-readout-kernel",
                "pair_readout_kernel",
                PairReadoutKernelFormula(),
                "Pair Readout Kernel",
                "Equality under the joint readout is exactly equality under both component readouts.",
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

private static Formula PairReadoutKernelFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Z")), Seq(F.Id("Type"))), Typed(Seq(F.Id("first")), Seq(F.Id("Concept"), Sp, F.Id("X"), Sp, F.Id("Y"))), Typed(Seq(F.Id("second")), Seq(F.Id("Concept"), Sp, F.Id("X"), Sp, F.Id("Z")))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("pairReadout"), Sp, F.Id("first"), Sp, F.Id("second"), Close, Sp, Eq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("first"), Sp, F.Id("infimum"), Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("second")));

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
