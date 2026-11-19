using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorBraidingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sector skew symmetry and finite braiding convolution",
        H("Sector skew symmetry and finite braiding convolution"),
        Blocks(
            Paragraph(Text(
                "The actual lattice state-field skew-symmetry law descends to arbitrary "
                    + "charge sectors. For every signed mode n, the canonical coefficient "
                    + "is a finite convolution of reversed-sector coefficients, with the "
                    + "charge-preserving translation power and the normalized factor "
                    + "(-1)^(n+j+1)/j!. The proof transports the all-state identity through "
                    + "single_canonical, the charge-sector translation law, and projection.")),
            Describe.Lean(
                DescribeId.Create("latticesectorbraiding-reverse-term"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.reverseTerm"),
                H("Finite sector braiding term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The jth charge-sector contribution to the skew-symmetry convolution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticesectorbraiding-canonical-skew"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorBraiding.canonical_skew"),
                H("Canonical sector skew symmetry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every canonical sector mode has finite reverse support and equals the "
                        + "corresponding finite braiding convolution."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This is a finite algebraic specialization of the existing actual "
                    + "state-field skew-symmetry supplier. It makes no claim of analytic "
                    + "convergence, a coherent tensor-category hexagon, a Monster module, "
                    + "or a physical CFT/string realization.")))));
}
