using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RationalGramCospectralDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/RationalGramCospectral";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cospectral rational unit Gram matrices with different minimum ambient dimensions.",
        H("Equal spectra and different rational coordinate counts"),
        Blocks(
            Definition("paired-edges", "pairedEdges", "Two disjoint weighted edges",
                "The diagonal entries are one. A pair of disjoint edges has weight twice the "
                + "parameter and all other off-diagonal entries equal the parameter."),
            Definition("triangle-block", "triangleBlock", "An isolated direction and a triangle",
                "The diagonal entries are one. The three edges in the triangle have weight "
                + "twice the parameter. The other off-diagonal entries are zero."),
            Definition("realizable-in", "RealizableIn", "Exact rational Gram realization",
                "The matrix is the product of a rational rectangular matrix with its transpose. "
                + "The number of columns is the ambient dimension."),
            Describe.Lean(DescribeId.Create("thresholds-on-conic"),
                DeclarationHandle.Create(Module + ".thresholds_on_conic"),
                H("Six- and seven-coordinate thresholds on a conic"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take nonzero rational numbers u and v with five times the "
                        + "square of u plus seven times the square of v equal to three. Set the "
                        + "parameter to one quarter of the difference between five times the "
                        + "square of u and one. The two Gram matrices have identical characteristic "
                        + "polynomials. The paired-edge matrix fits in n rational coordinates "
                        + "exactly when n is at least seven. The triangle-block matrix fits "
                        + "exactly when n is at least six.")),
                    Paragraph(Text("Rational eigenbases give the common characteristic polynomial. "
                        + "The conic allows rational rescaling to fixed quadratic forms. At the "
                        + "base point both examples have explicit orthogonal Gram factors at "
                        + "their respective thresholds. Aligning a partial frame with the same "
                        + "Gram data reduces both dimension lower bounds to ternary equations. "
                        + "A descent modulo seven excludes the paired-edge form in six coordinates. "
                        + "The three-square obstruction excludes the triangle-block form in five. "
                        + "Appending zero coordinates preserves each realization."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string id, string name, string title, string description) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);
}
