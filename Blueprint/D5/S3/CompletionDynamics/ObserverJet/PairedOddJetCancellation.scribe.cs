using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.ObserverJet;

internal sealed class PairedOddJetCancellationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection pairing cancels odd linear jets while preserving quadratic information in the even channel.",
        H("Paired Odd Jet Cancellation"),
        Blocks(
            Theorem(
                "even-add-odd-eq",
                "even_add_odd_eq",
                EvenAddOddEqFormula(),
                "Even Add Odd eq",
                "Every profile decomposes exactly into its paired even and odd channels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "even-channel-neg",
                "even_channel_neg",
                EvenChannelNegFormula(),
                "Even Channel neg",
                "The paired even channel is invariant under reflection.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "odd-channel-neg",
                "odd_channel_neg",
                OddChannelNegFormula(),
                "Odd Channel neg",
                "The paired odd channel changes sign under reflection.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "linear-jet-even-channel-zero",
                "linear_jet_even_channel_zero",
                LinearJetEvenChannelZeroFormula(),
                "Linear Jet Even Channel Zero",
                "A first-order signed jet vanishes after pairing in the even channel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "linear-jet-odd-channel",
                "linear_jet_odd_channel",
                LinearJetOddChannelFormula(),
                "Linear Jet Odd Channel",
                "The same first-order jet is retained exactly in the odd channel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "reflected-tangent-square",
                "reflected_tangent_square",
                ReflectedTangentSquareFormula(),
                "Reflected Tangent Square",
                "Squaring a reflected tangent removes its sign.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "quadratic-jet-even-channel",
                "quadratic_jet_even_channel",
                QuadraticJetEvenChannelFormula(),
                "Quadratic Jet Even Channel",
                "A quadratic jet survives reflection pairing in the even channel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "quadratic-jet-odd-channel-zero",
                "quadratic_jet_odd_channel_zero",
                QuadraticJetOddChannelZeroFormula(),
                "Quadratic Jet Odd Channel Zero",
                "A quadratic jet has zero odd component.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "paired-tangent-average-zero",
                "paired_tangent_average_zero",
                PairedTangentAverageZeroFormula(),
                "Paired Tangent Average Zero",
                "Direct vector-pair version of first-order cancellation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "paired-tangent-second-moment",
                "paired_tangent_second_moment",
                PairedTangentSecondMomentFormula(),
                "Paired Tangent Second Moment",
                "The second moment of a reflected tangent pair is the original square.",
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

private static Formula EvenAddOddEqFormula() => Statement(
    [Typed(Seq(F.Id("f")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("evenChannel"), Sp, F.Id("f"), Sp, F.Id("h"), Sp, Plus, Sp, F.Id("oddChannel"), Sp, F.Id("f"), Sp, F.Id("h"), Sp, Eq, Sp, F.Id("f"), Sp, F.Id("h")));

private static Formula EvenChannelNegFormula() => Statement(
    [Typed(Seq(F.Id("f")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("evenChannel"), Sp, F.Id("f"), Sp, Open, Minus, F.Id("h"), Close, Sp, Eq, Sp, F.Id("evenChannel"), Sp, F.Id("f"), Sp, F.Id("h")));

private static Formula OddChannelNegFormula() => Statement(
    [Typed(Seq(F.Id("f")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("oddChannel"), Sp, F.Id("f"), Sp, Open, Minus, F.Id("h"), Close, Sp, Eq, Sp, Minus, F.Id("oddChannel"), Sp, F.Id("f"), Sp, F.Id("h")));

private static Formula LinearJetEvenChannelZeroFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("evenChannel"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("v"), Sp, Times, Sp, F.Id("u"), Close, Sp, F.Id("h"), Sp, Eq, Sp, D(0)));

private static Formula LinearJetOddChannelFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("oddChannel"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("v"), Sp, Times, Sp, F.Id("u"), Close, Sp, F.Id("h"), Sp, Eq, Sp, F.Id("v"), Sp, Times, Sp, F.Id("h")));

private static Formula ReflectedTangentSquareFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(Open, Minus, F.Id("v"), Close, Sp, Caret, D(2), Sp, Eq, Sp, F.Id("v"), Sp, Caret, D(2)));

private static Formula QuadraticJetEvenChannelFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("evenChannel"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, Open, F.Id("v"), Sp, Times, Sp, F.Id("u"), Close, Sp, Caret, D(2), Close, Sp, F.Id("h"), Sp, Eq, Sp, Open, F.Id("v"), Sp, Times, Sp, F.Id("h"), Close, Sp, Caret, D(2)));

private static Formula QuadraticJetOddChannelZeroFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("oddChannel"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, Open, F.Id("v"), Sp, Times, Sp, F.Id("u"), Close, Sp, Caret, D(2), Close, Sp, F.Id("h"), Sp, Eq, Sp, D(0)));

private static Formula PairedTangentAverageZeroFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(Open, F.Id("v"), Sp, Plus, Sp, Open, Minus, F.Id("v"), Close, Close, Sp, Slash, Sp, D(2), Sp, Eq, Sp, D(0)));

private static Formula PairedTangentSecondMomentFormula() => Statement(
    [Typed(Seq(F.Id("v")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(Open, F.Id("v"), Sp, Caret, D(2), Sp, Plus, Sp, Open, Minus, F.Id("v"), Close, Sp, Caret, D(2), Close, Sp, Slash, Sp, D(2), Sp, Eq, Sp, F.Id("v"), Sp, Caret, D(2)));

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
