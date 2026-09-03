using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class CauchyFeatureRightInverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct supports away from one center give a nonsingular reciprocal Cauchy-jet feature matrix.",
        H("Cauchy-Feature Right Inverse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reciprocal-cauchy-node"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.reciprocalCauchyNode"),
                H("Reciprocal affine Cauchy node"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each support coordinate is translated by one center and inverted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cauchy-jet-feature-matrix"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureMatrix"),
                H("Cauchy-jet feature matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The matrix is a nonzero reciprocal diagonal factor times the existing Vandermonde matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cauchy-jet-feature-right-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchyJetFeatureRightInverse"),
                H("Canonical Cauchy-jet inverse"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical certificate is Mathlib's nonsingular matrix inverse."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cauchy-jet-feature-det-ne-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_jet_feature_det_ne_zero"),
                H("Distinct supports give a nonzero determinant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Injectivity survives common translation and inversion; the determinant then factors into a nonzero diagonal product and a nonzero Vandermonde determinant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cauchy-feature-right-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/CauchyFeatureRightInverse.cauchy_feature_right_inverse"),
                H("The Cauchy-jet inverse is two-sided"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonsingular inverse supplies both matrix inverse identities and an injective finite analysis map."))),
                DescribeRole.Theorem)
        ),
        []));
}
