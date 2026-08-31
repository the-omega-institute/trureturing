using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class GoldenRealizationCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/GoldenRealizationCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One certificate packages the quadratic, Fibonacci, rotation-trace, Mobius-fixed, and projective-attraction realizations of the golden structure while exhibiting a repelling countermodel.",
        H("Golden Realization Certificate"),
        Blocks(
            Theorem(
                "canonical-golden-cross-representation-certificate",
                "canonical_golden_cross_representation_certificate",
                CanonicalGoldenCrossRepresentationCertificateFormula(),
                "Canonical Golden Cross Representation Certificate",
                "The canonical golden structure satisfies the full cross-representation certificate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-repelling-affine-fixed",
                "golden_repelling_affine_fixed",
                GoldenRepellingAffineFixedFormula(),
                "Golden Repelling Affine Fixed",
                "The same golden point can be fixed in a different dynamical system.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-repelling-affine-has-deriv-at",
                "golden_repelling_affine_hasDerivAt",
                GoldenRepellingAffineHasderivatFormula(),
                "Golden Repelling Affine Has Deriv At",
                "The affine countermodel has derivative φ² at the fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-repelling-affine-multiplier-gt-one",
                "golden_repelling_affine_multiplier_gt_one",
                GoldenRepellingAffineMultiplierGtOneFormula(),
                "Golden Repelling Affine Multiplier Gt One",
                "The affine countermodel is strictly repelling.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-fixed-does-not-force-attraction",
                "golden_fixed_does_not_force_attraction",
                GoldenFixedDoesNotForceAttractionFormula(),
                "Golden Fixed Does Not Force Attraction",
                "Hence fixedness of the golden point alone does not imply attraction.",
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

private static Formula CanonicalGoldenCrossRepresentationCertificateFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("GoldenCrossRepresentationCertificate")));

private static Formula GoldenRepellingAffineFixedFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("goldenRepellingAffine"), Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula GoldenRepellingAffineHasderivatFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("HasDerivAt"), Sp, F.Id("goldenRepellingAffine"), Sp, Open, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Caret, D(2), Close, Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula GoldenRepellingAffineMultiplierGtOneFormula() => Statement(
    [],
        [],
        [],
        Seq(D(1), Sp, Lt, Sp, Bar, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Caret, D(2), Bar));

private static Formula GoldenFixedDoesNotForceAttractionFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("goldenRepellingAffine"), Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Land, Sp, D(1), Sp, Lt, Sp, Bar, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Caret, D(2), Bar));

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
