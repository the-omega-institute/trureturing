using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class ObserverSignedSupportBarcodeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/ObserverSignedSupportBarcode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observer-dependent signed support is negative exactly on an open orbit interval; "
            + "under positive masses, the finite count of negative localized weights equals "
            + "the number of active intervals.",
        H("Observer-Dependent Signed-Support Barcode"),
        Blocks(
            DefinitionNode(
                "observer-signed-support",
                "observerSignedSupport",
                "Observer-dependent signed support",
                "The squared observer-height displacement minus the squared transverse displacement."),
            DefinitionNode(
                "active-orbit-interval",
                "orbitActiveAt",
                "Active orbit interval",
                "The observer lies in the open interval centered at the orbit height with transverse radius."),
            DefinitionNode(
                "observer-localized-weight",
                "observerLocalizedWeight",
                "Observer-localized atomic weight",
                "Positive mass multiplies the observer-dependent signed support."),
            DefinitionNode(
                "active-orbit-count",
                "activeOrbitCount",
                "Active orbit count",
                "The finite number of orbit intervals containing the observation time."),
            DefinitionNode(
                "negative-localized-weight-count",
                "negativeLocalizedWeightCount",
                "Negative localized-weight count",
                "The finite number of strictly negative localized atomic weights."),
            Describe.Lean(
                DescribeId.Create("signed-support-is-negative-exactly-on-the-active-interval"),
                DeclarationHandle.Create(
                    Prefix + "observer_signed_support_neg_iff_active"),
                H("Signed support is negative exactly on the active interval"),
                StatementSource.FromAuthor(SupportNegativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inequality is the difference-of-squares test: the observer-height "
                        + "distance is smaller than the transverse displacement exactly when "
                        + "the signed support is negative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-mass-preserves-the-active-interval-sign-test"),
                DeclarationHandle.Create(
                    Prefix + "observer_localized_weight_neg_iff_active"),
                H("Positive mass preserves the active-interval sign test"),
                StatementSource.FromAuthor(WeightNegativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strict positivity of mass makes multiplication sign-reflecting, so no "
                        + "additional negative direction is introduced by the mass itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-weight-count-equals-active-interval-count"),
                DeclarationHandle.Create(
                    Prefix + "negative_localized_weight_count_eq_active_orbit_count"),
                H("Negative-weight count equals active-interval count"),
                StatementSource.FromAuthor(CountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two finite filters have pointwise equivalent membership under positive "
                        + "masses, hence their cardinalities agree exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-orbit-existence-equals-negative-weight-existence"),
                DeclarationHandle.Create(
                    Prefix + "exists_active_orbit_iff_exists_negative_localized_weight"),
                H("Active-orbit existence equals negative-weight existence"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the existential form of the barcode identity. It is still a "
                        + "statement about atomic diagonal weights, not sampled Gram inertia."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel")),
        ]));

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula SupportNegativityFormula() =>
        F.Disp(F.Id("observerSupportNegativeIffActive"));

    private static Formula WeightNegativityFormula() =>
        F.Disp(F.Id("positiveMassWeightNegativeIffActive"));

    private static Formula CountFormula() =>
        F.Disp(F.Id("negativeWeightCountEqualsActiveOrbitCount"));

    private static Formula ExistenceFormula() =>
        F.Disp(F.Id("existsActiveOrbitIffExistsNegativeWeight"));
}
