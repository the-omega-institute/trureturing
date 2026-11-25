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
            Describe.Lean(DescribeId.Create("spectrum-and-thresholds"),
                DeclarationHandle.Create(Module + ".spectrum_and_thresholds"),
                H("Common characteristic polynomial and rational coordinate thresholds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("One invertible rational matrix conjugates the paired-edge matrix "
                        + "to the triangle-block matrix for every rational parameter. "
                        + "The two matrices have identical "
                        + "characteristic polynomials. The roots counted with repetitions are one plus four "
                        + "times the parameter, one, and two copies of one minus twice the parameter. "
                        + "Take rational numbers u and v with five times the square of u plus "
                        + "seven times the square of v equal to three. Set the parameter to one "
                        + "quarter of the difference between five times the square of u and one. "
                        + "The paired-edge matrix fits in n rational coordinates exactly when n "
                        + "is at least seven. The triangle-block matrix fits exactly when n is "
                        + "at least six. At parameter zero, both matrices are the identity and "
                        + "have a four-coordinate realization.")),
                    Paragraph(Text("Rational eigenbases give the common characteristic polynomial. "
                        + "The conic allows rational rescaling to fixed quadratic forms. At the "
                        + "base point both examples have explicit orthogonal Gram factors at "
                        + "their respective thresholds. Aligning a partial frame with the same "
                        + "Gram data reduces both dimension lower bounds to ternary equations. "
                        + "A descent modulo seven excludes the paired-edge form in six coordinates. "
                        + "The three-square obstruction excludes the triangle-block form in five. "
                        + "Appending zero coordinates preserves each realization."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-seven-on-conic"),
                DeclarationHandle.Create(Module + ".five_seven_on_conic"),
                H("A conic with five and seven rational coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take rational u and v with u nonzero and five times the square "
                        + "of u plus four times the square of v equal to nine. Set t to one quarter "
                        + "of the difference between five thirds of the square of u and one. "
                        + "The paired-edge matrix is realizable in n rational coordinates exactly "
                        + "when n is at least five. The triangle-block matrix is realizable exactly "
                        + "when n is at least seven. The same similarity and common spectrum apply.")),
                    Paragraph(Text("At u = v = 1 the determinant is 20/27. Its numerator is not "
                        + "a square modulo three, so a square rational Gram factor is impossible. "
                        + "The triangle-block matrix reduces to an orthogonal frame with squared "
                        + "lengths 1, 1, 5, and 3. In six coordinates the complement of the first "
                        + "three directions would represent 3 by the form with weights 5, 1, 1. "
                        + "Clearing denominators gives an obstruction modulo eight when the "
                        + "denominator is odd. An even denominator forces all three coordinates "
                        + "even by reduction modulo four. Explicit rational Gram factors attain "
                        + "both bounds. The square classes of the two varying eigenvalues carry "
                        + "the bounds along the conic. At u = 0 the parameter is minus one quarter "
                        + "and the common rank drops to three."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("seven-five-on-conic"),
                DeclarationHandle.Create(Module + ".seven_five_on_conic"),
                H("A conic with seven and five rational coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take rational u and v such that the square of u plus fourteen "
                        + "times the square of v equals fifteen, and set t to one quarter of the "
                        + "difference between one fifth of the square of u and one. The paired-edge "
                        + "matrix is realizable in n rational coordinates exactly when n is at least "
                        + "seven. The triangle-block matrix is realizable exactly when n is at least "
                        + "five. Both matrices have the common spectrum above.")),
                    Paragraph(Text("At u = v = 1 the paired-edge form has an orthogonal basis with "
                        + "squared lengths 1, 5, 70, and 70. Align the first three directions in a "
                        + "putative six-coordinate realization. The remaining three-dimensional "
                        + "orthogonal complement has a rational orthogonal basis with squared "
                        + "lengths 5, 34, and 2380. Its squared length 70 is excluded by descent "
                        + "modulo seven. The triangle-block form reduces to squared lengths 15, 1, "
                        + "70, and 210. Their product is five times a rational square, excluding a "
                        + "four-coordinate factor. Explicit Gram factors attain both bounds. "
                        + "Rational rescaling preserves the two varying eigenvalue square classes "
                        + "along the conic."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string id, string name, string title, string description) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);
}
