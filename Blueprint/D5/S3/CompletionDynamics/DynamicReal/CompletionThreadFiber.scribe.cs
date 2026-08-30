using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.DynamicReal;

internal sealed class CompletionThreadFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/DynamicReal/CompletionThreadFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constant completed readout has a nontrivial thread fiber, while adjoining the blow-up origin restores injectivity and proves that no completed-value decoder can reconstruct every thread.",
        H("Completion Thread Fiber"),
        Blocks(
            Theorem(
                "completion-value-constant",
                "completion_value_constant",
                CompletionValueConstantFormula(),
                "Completion Value Constant",
                "Every pair of threads lies in the same zeroth-order completion fiber.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-value-not-injective",
                "completion_value_not_injective",
                CompletionValueNotInjectiveFormula(),
                "Completion Value Not Injective",
                "Zeroth-order completion is not injective.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "blowup-value-injective",
                "blowup_value_injective",
                BlowupValueInjectiveFormula(),
                "Blowup Value Injective",
                "The first blow-up readout is injective on this normalized thread family.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completed-jet-readout-injective",
                "completed_jet_readout_injective",
                CompletedJetReadoutInjectiveFormula(),
                "Completed Jet Readout Injective",
                "Adjoining the first jet to the completion value restores injectivity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-completion-value-decoder",
                "no_completion_value_decoder",
                NoCompletionValueDecoderFormula(),
                "No Completion Value Decoder",
                "No function of the completed value alone can recover every origin coefficient.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-completion-thread-reconstructor",
                "no_completion_thread_reconstructor",
                NoCompletionThreadReconstructorFormula(),
                "No Completion Thread Reconstructor",
                "Any putative reconstruction of the full normalized observer from the completed value would induce a forbidden origin decoder.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-fiber-contains-all-origins",
                "completion_fiber_contains_all_origins",
                CompletionFiberContainsAllOriginsFormula(),
                "Completion Fiber Contains All Origins",
                "The common completion fiber is infinite, witnessed by the embedding of all real origin coefficients.",
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

private static Formula CompletionValueConstantFormula() => Statement(
    [Typed(Seq(F.Id("o"), Underscore, Grp(D(1))), Seq(F.Id("GoldenThreadObserver"))), Typed(Seq(F.Id("o"), Underscore, Grp(D(2))), Seq(F.Id("GoldenThreadObserver")))],
        [],
        [],
        Seq(F.Id("completionValue"), Sp, F.Id("o"), Underscore, Grp(D(1)), Sp, Eq, Sp, F.Id("completionValue"), Sp, F.Id("o"), Underscore, Grp(D(2))));

private static Formula CompletionValueNotInjectiveFormula() => Statement(
    [],
        [],
        [],
        Seq(Neg, Sp, F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("completionValue")));

private static Formula BlowupValueInjectiveFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("blowupValue")));

private static Formula CompletedJetReadoutInjectiveFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("completedJetReadout")));

private static Formula NoCompletionValueDecoderFormula() => Statement(
    [],
        [],
        [],
        Seq(Neg, Sp, Exists, Sp, F.Id("decode"), Sp, Colon, Sp, new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R")))), Comma, Sp, Forall, Sp, F.Id("observer"), Sp, Colon, Sp, F.Id("GoldenThreadObserver"), Comma, Sp, F.Id("decode"), Sp, Open, F.Id("completionValue"), Sp, F.Id("observer"), Close, Sp, Eq, Sp, F.Id("observer"), Dot, F.Id("origin")));

private static Formula NoCompletionThreadReconstructorFormula() => Statement(
    [],
        [],
        [],
        Seq(Neg, Sp, Exists, Sp, F.Id("reconstruct"), Sp, Colon, Sp, new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(F.Id("GoldenThreadObserver"))), Comma, Sp, Forall, Sp, F.Id("observer"), Sp, Colon, Sp, F.Id("GoldenThreadObserver"), Comma, Sp, F.Id("reconstruct"), Sp, Open, F.Id("completionValue"), Sp, F.Id("observer"), Close, Sp, Eq, Sp, F.Id("observer")));

private static Formula CompletionFiberContainsAllOriginsFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("completionValue"), Sp, Langle, Sp, F.Id("c"), Sp, Rangle, Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

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
