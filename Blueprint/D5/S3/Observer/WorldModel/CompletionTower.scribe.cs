using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class CompletionTowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/CompletionTower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent fixed threads define truth in a typed completion tower.",
        H("Completion Tower"),
        Blocks(
            Theorem(
                "transport-from-base-zero",
                "transportFromBase_zero",
                TransportfrombaseZeroFormula(),
                "Transport From Base Zero",
                "This theorem establishes transport from base zero in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "transport-from-base-succ",
                "transportFromBase_succ",
                TransportfrombaseSuccFormula(),
                "Transport From Base Succ",
                "This theorem establishes transport from base succ in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "transport-from-base-coherent",
                "transport_from_base_coherent",
                TransportFromBaseCoherentFormula(),
                "Transport From Base Coherent",
                "The recursively transported thread is coherent by construction.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "transport-from-fixed-base-is-fixed",
                "transport_from_fixed_base_is_fixed",
                TransportFromFixedBaseIsFixedFormula(),
                "Transport From Fixed Base Is Fixed",
                "Fixedness of one base state propagates to every completion level.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "transport-from-fixed-base-is-truth",
                "transport_from_fixed_base_is_truth",
                TransportFromFixedBaseIsTruthFormula(),
                "Transport From Fixed Base Is Truth",
                "A fixed base state canonically generates a truth thread.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "coherent-thread-eq-transport-from-base",
                "coherent_thread_eq_transport_from_base",
                CoherentThreadEqTransportFromBaseFormula(),
                "Coherent Thread eq Transport From Base",
                "Every coherent thread is determined by its base coordinate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "coherent-threads-ext",
                "coherent_threads_ext",
                CoherentThreadsExtFormula(),
                "Coherent Threads Ext",
                "Two coherent threads with the same base state are equal.",
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

private static Formula TransportfrombaseZeroFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("base")), Seq(F.Id("tower"), Dot, F.Id("State"), Sp, D(0)))],
        [],
        [],
        Seq(F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, F.Id("base"), Sp, D(0), Sp, Eq, Sp, F.Id("base")));

private static Formula TransportfrombaseSuccFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("base")), Seq(F.Id("tower"), Dot, F.Id("State"), Sp, D(0))), Typed(Seq(F.Id("level")), Seq(Mathbb, Grp(F.Id("N"))))],
        [],
        [],
        Seq(F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, F.Id("base"), Sp, Open, F.Id("level"), Sp, Plus, Sp, D(1), Close, Sp, Eq, Sp, F.Id("tower"), Dot, F.Id("bond"), Sp, F.Id("level"), Sp, Open, F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, F.Id("base"), Sp, F.Id("level"), Close));

private static Formula TransportFromBaseCoherentFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("base")), Seq(F.Id("tower"), Dot, F.Id("State"), Sp, D(0)))],
        [],
        [],
        Seq(F.Id("IsCoherentThread"), Sp, F.Id("tower"), Sp, Open, F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, F.Id("base"), Close));

private static Formula TransportFromFixedBaseIsFixedFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("base")), Seq(F.Id("tower"), Dot, F.Id("State"), Sp, D(0)))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, Open, F.Id("tower"), Dot, F.Id("dynamics"), Sp, D(0), Close, Sp, F.Id("base"))],
        Seq(F.Id("IsFixedThread"), Sp, F.Id("tower"), Sp, Open, F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, F.Id("base"), Close));

private static Formula TransportFromFixedBaseIsTruthFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("base")), Seq(F.Id("tower"), Dot, F.Id("State"), Sp, D(0)))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, Open, F.Id("tower"), Dot, F.Id("dynamics"), Sp, D(0), Close, Sp, F.Id("base"))],
        Seq(F.Id("IsTruthThread"), Sp, F.Id("tower"), Sp, Open, F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, F.Id("base"), Close));

private static Formula CoherentThreadEqTransportFromBaseFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("thread")), Seq(F.Id("Thread"), Sp, F.Id("tower")))],
        [],
        [Seq(F.Id("IsCoherentThread"), Sp, F.Id("tower"), Sp, F.Id("thread"))],
        Seq(F.Id("thread"), Sp, Eq, Sp, F.Id("transportFromBase"), Sp, F.Id("tower"), Sp, Open, F.Id("thread"), Sp, D(0), Close));

private static Formula CoherentThreadsExtFormula() => Statement(
    [Typed(Seq(F.Id("tower")), Seq(F.Id("Tower"))), Typed(Seq(F.Id("first")), Seq(F.Id("Thread"), Sp, F.Id("tower"))), Typed(Seq(F.Id("second")), Seq(F.Id("Thread"), Sp, F.Id("tower")))],
        [],
        [Seq(F.Id("IsCoherentThread"), Sp, F.Id("tower"), Sp, F.Id("first")), Seq(F.Id("IsCoherentThread"), Sp, F.Id("tower"), Sp, F.Id("second")), Seq(F.Id("first"), Sp, D(0), Sp, Eq, Sp, F.Id("second"), Sp, D(0))],
        Seq(F.Id("first"), Sp, Eq, Sp, F.Id("second")));

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
