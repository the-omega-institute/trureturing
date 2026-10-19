using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class SpectralFormulaDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/SpectralFormula.";
    private static LibraryNoteRef Original => LibraryNoteRef.Create("D5/L/Entropy/jozsa1994subentropy");
    private static LibraryNoteRef Later => LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant integral agrees with the finite spectral subentropy formula for distinct positive probabilities.",
        H("The simple-spectrum subentropy formula"), Blocks(
            Describe.Lean(DescribeId.Create("subentropy-spectral-coefficient"),
                DeclarationHandle.Create(Owner + "spectralCoefficient"),
                H("Spectral residue coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Original),
                Blocks(Paragraph(Text("For a real vector p on a finite type of cardinality N, the coefficient at i is p_i to exponent N divided by the product of p_i−p_j over all j distinct from i. The formula becomes the classical subentropy residue on positive distinct probability vectors. The total Lean definition also exists at coincident coordinates, but its zero-denominator convention does not define the paper's continuous extension."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("subentropy-diagonal-distinct-formula"),
                DeclarationHandle.Create(Owner + "matrixSubentropy_diagonal_eq_distinct_formula"),
                H("Agreement with the finite spectral formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Later),
                Blocks(
                    Paragraph(Text("For every finite type with decidable equality, every strictly positive real vector p with sum one and injective coordinates satisfies the following identity: the determinant integral of diagonal p equals the negative sum, over i, of p_i to exponent N times log p_i divided by the product of p_i−p_j over j distinct from i. N is the cardinality of the entire index type. Injectivity means pairwise distinct entries; there is no ordering hypothesis. The logarithm is natural.")),
                    Paragraph(Text("The finite spectral formula is attributed to the original subentropy literature and the later properties paper. The determinant-integral representation and its proof of agreement are repository derivations. Lagrange interpolation is applied to the degree-below-N polynomial formed by subtracting X to exponent N from the product of X+p_i. Evaluating at the distinct nodes −p_i gives the residue coefficients. The coefficient of X to exponent N−1 proves that their sum is one.")),
                    Paragraph(Text("Dividing the interpolated identity by the nonzero product of t+p_i gives the kernel as a finite weighted sum of reciprocal differences 1/(t+p_i)−1/(t+1). Each difference is integrated as a single integrable function; its two reciprocal terms are not separated. Strict positivity and total mass one give 0<p_i≤1, so the existing reciprocal-difference integral applies to each coefficient. Negative residue coefficients are allowed, and the finite integral interchange uses integrability rather than a positivity assumption on those coefficients.")),
                    Paragraph(Text("This theorem covers positive simple spectra and does not evaluate the quotient at repeated or zero entries. DensityKernel proves continuity of the determinant integral on positive trace-one matrices, including the boundary. Positive simple probability vectors are dense: mix an arbitrary probability vector p with a strictly positive distinct vector q, and choose positive mixing parameters tending to zero while avoiding the finitely many values at which a pair of coordinates coincides. Every coordinate is positive, and each pair can coincide at at most one parameter because q has distinct coordinates. Thus the simple-spectrum identity and continuity determine the continuous extension. StrongSubadditivityRefutation proves the density and uniqueness bridge as a consumed private theorem: ordered positive perturbations converge in a fixed eigenbasis, and continuity identifies every invariant spectral family with the determinant integral. Source metadata boundaries remain in the cited library notes."))),
                DescribeRole.Theorem))));
}
