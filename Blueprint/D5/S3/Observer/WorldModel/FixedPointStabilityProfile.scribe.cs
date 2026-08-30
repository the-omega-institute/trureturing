using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class FixedPointStabilityProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/FixedPointStabilityProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fixed-point stability is a separate multiplier profile whose canonical golden projective radius is positive, strictly below one, and sharper than the ambient stable ratio.",
        H("Fixed Point Stability Profile"),
        Blocks(
            Theorem(
                "uniform-radius-bound-each-attracting",
                "uniform_radius_bound_each_attracting",
                UniformRadiusBoundEachAttractingFormula(),
                "Uniform Radius Bound Each Attracting",
                "Every coordinate of a uniformly bounded profile is strictly attracting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "uniform-radius-bound-mono",
                "uniform_radius_bound_mono",
                UniformRadiusBoundMonoFormula(),
                "Uniform Radius Bound Mono",
                "Enlarging a valid radius below one preserves validity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-radius-pos",
                "golden_projective_radius_pos",
                GoldenProjectiveRadiusPosFormula(),
                "Golden Projective Radius pos",
                "The golden projective radius is positive.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "abs-golden-multiplier-eq-radius",
                "abs_golden_multiplier_eq_radius",
                AbsGoldenMultiplierEqRadiusFormula(),
                "Abs Golden Multiplier eq Radius",
                "The absolute golden completion multiplier is exactly its positive radius.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-radius-lt-one",
                "golden_projective_radius_lt_one",
                GoldenProjectiveRadiusLtOneFormula(),
                "Golden Projective Radius lt One",
                "The canonical projective golden system is strictly attracting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-multiplier-neg",
                "golden_projective_multiplier_neg",
                GoldenProjectiveMultiplierNegFormula(),
                "Golden Projective Multiplier neg",
                "Its multiplier is negative, recording the alternating side of approach.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-radius-lt-ambient-radius",
                "golden_projective_radius_lt_ambient_radius",
                GoldenProjectiveRadiusLtAmbientRadiusFormula(),
                "Golden Projective Radius lt Ambient Radius",
                "Projective normalization contracts more strongly than the ambient stable ratio φ⁻¹.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-constant-profile-uniform",
                "golden_constant_profile_uniform",
                GoldenConstantProfileUniformFormula(),
                "Golden Constant Profile Uniform",
                "A world-model family whose every local multiplier is the canonical golden projective multiplier has the exact uniform radius φ⁻².",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-constant-profile-is-uniformly-attracting",
                "golden_constant_profile_is_uniformly_attracting",
                GoldenConstantProfileIsUniformlyAttractingFormula(),
                "Golden Constant Profile Is Uniformly Attracting",
                "The canonical golden constant profile is uniformly attracting.",
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

private static Formula UniformRadiusBoundEachAttractingFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type"))), Typed(Seq(F.Id("multiplier")), new Formula.TypeArrow(Seq(F.Id("Index")), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("radius")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("i")), Seq(F.Id("Index")))],
        [],
        [Seq(F.Id("UniformRadiusBound"), Sp, F.Id("multiplier"), Sp, F.Id("radius"))],
        Seq(Bar, F.Id("multiplier"), Sp, F.Id("i"), Bar, Sp, Lt, Sp, D(1)));

private static Formula UniformRadiusBoundMonoFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type"))), Typed(Seq(F.Id("multiplier")), new Formula.TypeArrow(Seq(F.Id("Index")), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("small")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("large")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("UniformRadiusBound"), Sp, F.Id("multiplier"), Sp, F.Id("small")), Seq(F.Id("small"), Sp, Leq, Sp, F.Id("large")), Seq(F.Id("large"), Sp, Lt, Sp, D(1))],
        Seq(F.Id("UniformRadiusBound"), Sp, F.Id("multiplier"), Sp, F.Id("large")));

private static Formula GoldenProjectiveRadiusPosFormula() => Statement(
    [],
        [],
        [],
        Seq(D(0), Sp, Lt, Sp, F.Id("goldenProjectiveRadius")));

private static Formula AbsGoldenMultiplierEqRadiusFormula() => Statement(
    [],
        [],
        [],
        Seq(Bar, F.Id("goldenProjectiveMultiplier"), Bar, Sp, Eq, Sp, F.Id("goldenProjectiveRadius")));

private static Formula GoldenProjectiveRadiusLtOneFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenProjectiveRadius"), Sp, Lt, Sp, D(1)));

private static Formula GoldenProjectiveMultiplierNegFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenProjectiveMultiplier"), Sp, Lt, Sp, D(0)));

private static Formula GoldenProjectiveRadiusLtAmbientRadiusFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenProjectiveRadius"), Sp, Lt, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Caret, Grp(Minus, D(1))));

private static Formula GoldenConstantProfileUniformFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type")))],
        [],
        [],
        Seq(F.Id("UniformRadiusBound"), Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Colon, Sp, F.Id("Index"), Sp, Mapsto, Sp, F.Id("goldenProjectiveMultiplier"), Close, Sp, F.Id("goldenProjectiveRadius")));

private static Formula GoldenConstantProfileIsUniformlyAttractingFormula() => Statement(
    [Typed(Seq(F.Id("Index")), Seq(F.Id("Type")))],
        [],
        [],
        Seq(F.Id("IsUniformlyAttracting"), Sp, Open, LambdaLower, Sp, F.Id("value"), Sp, Colon, Sp, F.Id("Index"), Sp, Mapsto, Sp, F.Id("goldenProjectiveMultiplier"), Close));

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
