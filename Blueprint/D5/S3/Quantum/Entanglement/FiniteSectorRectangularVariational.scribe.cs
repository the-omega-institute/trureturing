using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorRectangularVariationalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular singular-value prefix bounds used by the passive sector test.",
        H("Rectangular Variational Bound"),
        Blocks(
            Paragraph(Text(
                "The Ky Fan sum is the sum of the first k singular values of a finite "
                + "linear map between real or complex inner-product spaces. The domain and "
                + "codomain dimensions may differ. These selected arguments adapt "
                + "AIQ-Kitware/aiq-dkps-formalization revision "
                + "64e234954217f3ca907ac980c8cbde2900109a66 under Apache-2.0. "
                + "The port retires when this repository's pinned Mathlib has equivalent results.")),
            Describe.Lean(
                DescribeId.Create("finite-sector-ky-fan-sum"),
                DeclarationHandle.Create(Owner + "kyFanSum"),
                H("Ky Fan singular-value sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural prefix length k, sum the first k singular values, with "
                    + "zero extension beyond the source dimension."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-sector-rectangular-variational-upper"),
                DeclarationHandle.Create(Owner + "re_sum_inner_map_le_ky_fan_sum"),
                H("Orthonormal variational upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every pair of orthonormal k-families has real paired trace at most the "
                    + "Ky Fan sum. The proof passes through positive square roots, polar "
                    + "structure and a self-adjoint zero extension; the rectangular estimate "
                    + "does not assume equal dimensions."))),
                DescribeRole.Theorem))));
}
