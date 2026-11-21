using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoGeodesicModularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geodesic relative entropy as a spectral quadratic form in matrix-unit coordinates.",
        H("The geodesic modular operator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geodesic-modular-geodesicaction"),
                DeclarationHandle.Create(Prefix + "geodesicAction"),
                H("Action on Hilbert–Schmidt matrices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (52) left-multiplies by the first matrix to the power 1−t and right-multiplies by its t-th power conjugated by the inverse square root of the second matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("geodesic-modular-geodesicmodular"),
                DeclarationHandle.Create(Prefix + "geodesicModular"),
                H("Matrix of the modular operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The column indexed by a matrix unit contains the coordinates of its image under the action in equation (52)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("geodesic-modular-weightedvector"),
                DeclarationHandle.Create(Prefix + "weightedVector"),
                H("Coordinates of the reference square root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vector lists the entries of the square root of the second matrix. It represents the Hilbert–Schmidt vector in equation (59)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("geodesic-modular-geodesicrelativeentropy"),
                DeclarationHandle.Create(Prefix + "geodesicRelativeEntropy"),
                H("Geodesic relative entropy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equations (59) and (63) pair the result of applying the spectral function z ↦ z log z of the modular matrix to the reference vector with that same vector. Lean takes the real part of the complex quadratic form."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("geodesic-modular-geodesicmodular-eq-kronecker"),
                DeclarationHandle.Create(Prefix + "geodesicModular_eq_kronecker"),
                H("Kronecker representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In the chosen ordering of matrix units, the right multiplication factor is transposed in the Kronecker representation. The left factor is the (1−t)-th power of the first matrix."))),
                DescribeRole.Theorem)),
        []));
}
