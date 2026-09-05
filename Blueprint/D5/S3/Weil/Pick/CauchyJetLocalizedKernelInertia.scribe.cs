using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class CauchyJetLocalizedKernelInertiaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A distinct signed-support Cauchy-jet sampling has negative index exactly equal to the active reflected-orbit count.",
        H("Cauchy-Jet Localized-Kernel Inertia"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-support-profile"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportProfile"),
                H("Observer signed-support profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite profile evaluates the signed-support coordinate for every orbit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-support-complex"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportComplex"),
                H("Complex support embedding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real signed-support profile is embedded into the complex plane."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-localized-weight-profile"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedWeightProfile"),
                H("Localized weight profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each signed support is multiplied by its supplied positive mass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-cauchy-jet-feature-matrix"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerCauchyJetFeatureMatrix"),
                H("Canonical observer Cauchy-jet feature matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sampling center is fixed at i, which avoids every real signed-support coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-localized-cauchy-jet-gram"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGram"),
                H("Localized Cauchy-jet Gram matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed diagonal form is pulled back through the canonical finite Cauchy-jet feature matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-localized-cauchy-jet-gram-hermitian"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGramIsHermitian"),
                H("Localized Gram Hermitian witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Hermitianity is inherited from conjugate-transpose pullback of the real diagonal form."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cauchy-jet-localized-kernel-barcode-inertia"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.cauchy_jet_localized_kernel_barcode_inertia"),
                H("Sampled negative index equals the active barcode count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Distinct signed supports make the feature matrix invertible. Inertia therefore equals diagonal sign count, and positive masses identify that count with active reflected-orbit intervals. Positive negative-index and zero negative-index characterizations are included."))),
                DescribeRole.Theorem)
        ),
        []));
}
