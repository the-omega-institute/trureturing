using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeConvolutionFockAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native finite creation-translation convolution transpose",
        ArtifactId.Parse("D5/S3/VertexAlgebra/LatticeConvolutionFockAdjoint"),
        "D5.S3.VertexAlgebra.LatticeConvolutionFockAdjoint",
        Blocks(
            Paragraph(Text("The operator is literally convolution(alpha,s,translatedPolynomial(alpha,p)) from LatticeActualProductKernel, with every integer s and every finite native oscillator polynomial p. No alternative field, abstract invariant form, positivity premise, inverse Gram matrix or occupation cutoff replaces it.")),
            Paragraph(Text("Finite polynomial induction supplies the constant-term convolution calculation: only the summand whose shifted creation index is zero survives. Negative indices vanish by the native definitions. The creation-coefficient adjoint therefore supplies the vacuum step of the full transpose induction.")),
            Paragraph(Text("The generator step uses the actual translated-variable product identity and the existing convolution_X_pow shift. That supplier proves the integer reindexing on finite monomials, not an interchange of infinite operator sums. The existing annihilation_convolution and annihilation_transport identities give the matching annihilator recurrence after cancelling the nonzero frequency. Induction on the full left polynomial, generalizing the integer index and right polynomial, reverses the actual composition.")),
            Paragraph(Text("All lattice ranks and all singular or indefinite integral Gram forms remain in scope. This is standard lattice Fock mathematics, with zero novelty claimed. This transpose by itself does not give all-descendant opposite modes, Sugawara L1 local nilpotence, ghost or original-Q adjoints, physical cohomology isometry, no-ghost, moonshine, full string theory or AdS/CFT.")),
            Describe.Lean(
                DescribeId.Create("latticeconvolutionfockadjoint-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeConvolutionFockAdjoint.convolution_transpose"),
                H("All-integer native convolution transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every alpha, integer s, and polynomials p and q, fockForm(convolution(alpha,s,translatedPolynomial(alpha,p)),q) equals fockForm(p,convolution(-alpha,-s,translatedPolynomial(-alpha,q))). Every operation is on an actual finite polynomial."))),
                DescribeRole.Theorem))));
}
