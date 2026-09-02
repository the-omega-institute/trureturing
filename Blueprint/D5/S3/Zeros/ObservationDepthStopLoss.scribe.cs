using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class ObservationDepthStopLossDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/ObservationDepthStopLoss.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite stop-loss depth profiles satisfy sharp positivity, cutoff, saturation, "
            + "and linear-regime bounds.",
        H("Observation-Depth Stop-Loss Profile"),
        Blocks(
            DefinitionNode(
                "active-pole-height",
                "activePoleHeight",
                "Active pole height",
                "The positive part of delta minus the observation depth."),
            DefinitionNode(
                "horizontal-tail-count",
                "horizontalTailCount",
                "Horizontal tail count",
                "The multiplicity sum over poles whose distance exceeds the observation depth."),
            DefinitionNode(
                "remaining-depth",
                "remainingDepth",
                "Remaining depth",
                "The multiplicity-weighted sum of active pole heights."),
            DefinitionNode(
                "double-depth-decay",
                "doubleDepthDecay",
                "Double-depth decay",
                "The multiplicity-weighted sum of the increment capped by each active height."),
            Describe.Lean(
                DescribeId.Create("observation-depth-stop-loss"),
                DeclarationHandle.Create(Prefix + "observation_depth_stop_loss"),
                H("Sharp finite stop-loss bounds"),
                StatementSource.FromAuthor(MainTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source atom ends immediately after introducing the four displayed "
                            + "quantities. The formal statement therefore records their finite-sum "
                            + "well-formedness without importing the next atom's transport laws.")),
                    Paragraph(Text(
                        "Positive transverse distances give the initial tail and remaining-depth "
                            + "values. A nonnegative increment makes the decay nonnegative and "
                            + "bounds it by both remaining depth and increment times total "
                            + "multiplicity.")),
                    Paragraph(Text(
                        "Complete cutoff, complete saturation, and the linear regime provide exact "
                            + "equality cases for every displayed inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonpositive-distance-breaks-initial-activity"),
                DeclarationHandle.Create(
                    Prefix + "nonpositive_distance_breaks_initial_activity"),
                H("Nonpositive distance breaks initial activity"),
                StatementSource.FromAuthor(NonpositiveDistanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One pole at distance zero with multiplicity one has zero active tail count "
                        + "at depth zero, rather than total multiplicity one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-depth-breaks-decay-nonnegativity"),
                DeclarationHandle.Create(Prefix + "negative_depth_breaks_decay_nonnegativity"),
                H("Negative depth breaks decay nonnegativity"),
                StatementSource.FromAuthor(NegativeDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one unit-distance pole of unit multiplicity, increment minus one gives "
                        + "double-depth decay minus one. Thus y must be nonnegative."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula MainTheoremFormula()
    {
        Formula delta = F.DeltaLower;
        Formula omega = F.Omega;
        Formula y = F.Id("y");
        Formula j = F.Id("j");
        Formula m = F.Id("m");
        Formula h = F.Id("h");
        Formula n = F.Id("N");
        Formula r = F.Id("R");
        Formula a = F.Id("A");
        Formula total = Sum(Subscript(m, j));
        Formula weightedDistance = Sum(Multiply(Subscript(m, j), Subscript(delta, j)));
        Formula height = Apply(h, j, omega);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, j, Comma, Sp, Subscript(delta, j), Sp, Gt, Sp, D(0),
                Comma, Sp, y, Sp, Geq, Sp, D(0), Sp, Rightarrow),
            Seq(Apply(n, D(0)), Sp, Eq, Sp, total, Sp, Land, Sp,
                Apply(r, D(0)), Sp, Eq, Sp, weightedDistance, Sp, Land, Sp,
                Apply(a, omega, D(0)), Sp, Eq, Sp, D(0), Comma),
            Seq(D(0), Sp, Leq, Sp, Apply(r, omega), Sp, Land, Sp,
                D(0), Sp, Leq, Sp, Apply(a, omega, y), Sp, Leq, Sp,
                Apply(r, omega), Comma),
            Seq(Apply(a, omega, y), Sp, Leq, Sp, Multiply(y, total), Comma),
            Seq(Open, Forall, Sp, j, Comma, Sp, Subscript(delta, j), Sp, Leq, Sp, omega,
                Close, Sp, Rightarrow, Sp, Apply(r, omega), Sp, Eq, Sp, D(0), Sp,
                Land, Sp, Apply(a, omega, y), Sp, Eq, Sp, D(0), Comma),
            Seq(Open, Forall, Sp, j, Comma, Sp, height, Sp, Leq, Sp, y, Close,
                Sp, Rightarrow, Sp, Apply(a, omega, y), Sp, Eq, Sp, Apply(r, omega), Comma),
            Seq(Open, Forall, Sp, j, Comma, Sp, y, Sp, Leq, Sp, height, Close,
                Sp, Rightarrow, Sp, Apply(a, omega, y), Sp, Eq, Sp,
                Multiply(y, total), Dot),
        ]));
    }

    private static Formula NonpositiveDistanceFormula() => Disp(Seq(
        Apply(F.Id("N"), D(0)), Sp, Eq, Sp, D(0), Sp, Neq, Sp, D(1), Sp, Eq, Sp,
        Sum(Subscript(F.Id("m"), F.Id("j"))), Dot));

    private static Formula NegativeDepthFormula() => Disp(Seq(
        Apply(F.Id("A"), D(0), Seq(Minus, D(1))), Sp, Eq, Sp, Seq(Minus, D(1)),
        Sp, Lt, Sp, D(0), Dot));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Subscript(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Sum(Formula body) =>
        Seq(Subscript(F.Sum, F.Id("j")), Sp, body);
}
