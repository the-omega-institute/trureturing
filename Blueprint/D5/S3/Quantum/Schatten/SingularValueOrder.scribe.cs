using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class SingularValueOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Loewner order and sorted singular values.", H("SingularValueOrder"), Blocks(
            Paragraph(Text("The sorted singular values of a complex square matrix are the square roots of the decreasingly ordered eigenvalues of its Gram matrix. The sorting step uses the multiset equality between the indexed eigenvalues and their ordered coordinates, with monotonicity of the square root.")),
            Paragraph(Text("Courant–Fischer supplies a spectral subspace for the smaller Hermitian form and a unit vector in that subspace on which the larger form is bounded by its selected eigenvalue. Positivity of the difference then compares the two selected eigenvalues. Applied to Gram matrices, this proves monotonicity of every sorted singular value.")),
            Paragraph(Text("The same spectral coordinates give invariance under unitary left multiplication and adjoints, and homogeneity under nonnegative real scaling. Spectral scaling is obtained from both Courant–Fischer bounds; no simplicity or invertibility assumption on the eigenvalues is required. These classical comparisons are used in the lower Gelfand–Naimark inequality.")))));
}
