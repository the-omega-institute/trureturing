using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class CompletionTowerMorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/CompletionTowerMorphism.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural wormholes transport fixed threads between completion towers.",
        H("Completion Tower Morphism"),
        Blocks(
            Theorem(
                "map-thread-coherent",
                "map_thread_coherent",
                TowermorphismMapThreadCoherentFormula(),
                "Map Thread Coherent",
                "Naturality transports coherent threads.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "map-thread-fixed",
                "map_thread_fixed",
                TowermorphismMapThreadFixedFormula(),
                "Map Thread Fixed",
                "Levelwise semiconjugacy transports fixed threads.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "map-truth-thread",
                "map_truth_thread",
                TowermorphismMapTruthThreadFormula(),
                "Map Truth Thread",
                "Every tower morphism transports truth threads.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "map-thread-compose",
                "mapThread_compose",
                TowermorphismMapthreadComposeFormula(),
                "Map Thread Compose",
                "Coordinatewise transport respects composition.",
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

private static Formula TowermorphismMapThreadCoherentFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("target")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("morphism")), Seq(F.Id("TowerMorphism"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("thread")), Seq(F.Id("Thread"), Sp, F.Id("source")))],
        [],
        [Seq(F.Id("IsCoherentThread"), Sp, F.Id("source"), Sp, F.Id("thread"))],
        Seq(F.Id("IsCoherentThread"), Sp, F.Id("target"), Sp, Open, F.Id("morphism"), Dot, F.Id("mapThread"), Sp, F.Id("thread"), Close));

private static Formula TowermorphismMapThreadFixedFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("target")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("morphism")), Seq(F.Id("TowerMorphism"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("thread")), Seq(F.Id("Thread"), Sp, F.Id("source")))],
        [],
        [Seq(F.Id("IsFixedThread"), Sp, F.Id("source"), Sp, F.Id("thread"))],
        Seq(F.Id("IsFixedThread"), Sp, F.Id("target"), Sp, Open, F.Id("morphism"), Dot, F.Id("mapThread"), Sp, F.Id("thread"), Close));

private static Formula TowermorphismMapTruthThreadFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("target")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("morphism")), Seq(F.Id("TowerMorphism"), Sp, F.Id("source"), Sp, F.Id("target"))), Typed(Seq(F.Id("thread")), Seq(F.Id("Thread"), Sp, F.Id("source")))],
        [],
        [Seq(F.Id("IsTruthThread"), Sp, F.Id("source"), Sp, F.Id("thread"))],
        Seq(F.Id("IsTruthThread"), Sp, F.Id("target"), Sp, Open, F.Id("morphism"), Dot, F.Id("mapThread"), Sp, F.Id("thread"), Close));

private static Formula TowermorphismMapthreadComposeFormula() => Statement(
    [Typed(Seq(F.Id("source")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("middle")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("target")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("second")), Seq(F.Id("TowerMorphism"), Sp, F.Id("middle"), Sp, F.Id("target"))), Typed(Seq(F.Id("first")), Seq(F.Id("TowerMorphism"), Sp, F.Id("source"), Sp, F.Id("middle"))), Typed(Seq(F.Id("thread")), Seq(F.Id("Thread"), Sp, F.Id("source")))],
        [],
        [],
        Seq(Open, F.Id("compose"), Sp, F.Id("second"), Sp, F.Id("first"), Close, Dot, F.Id("mapThread"), Sp, F.Id("thread"), Sp, Eq, Sp, F.Id("second"), Dot, F.Id("mapThread"), Sp, Open, F.Id("first"), Dot, F.Id("mapThread"), Sp, F.Id("thread"), Close));

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
