using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteHermitianSignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Foundation/FiniteHermitianSign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spectral sign of a finite Hermitian matrix vanishes on its kernel and attains its trace norm.",
        H("The finite Hermitian sign"),
        Blocks(
            Def("hermitianSign", "The Hermitian spectral sign",
                "Apply the real sign function to each eigenvalue in an orthonormal spectral basis. The values on strictly positive, zero and strictly negative eigenvalues are 1, 0 and −1."),
            Def("positiveSubspace", "The strictly positive spectral subspace",
                "Take the complex span of the spectral basis vectors whose eigenvalues are strictly positive."),
            Def("negativeSubspace", "The strictly negative spectral subspace",
                "Take the complex span of the spectral basis vectors whose eigenvalues are strictly negative."),
            Thm("hermitianSign_eigenspaces", "Kernel and extremal eigenspaces of the sign",
                "The sign has the same kernel as the original Hermitian matrix. Its +1 and −1 eigenspaces are the strictly positive and strictly negative spectral subspaces, respectively."),
            Thm("hermitianSign_spec", "The sign attains the trace norm",
                "The sign is Hermitian and both I−H and I+H are positive semidefinite for H the sign. Multiplying by the original Hermitian matrix replaces each eigenvalue by its absolute value. The real trace pairing is therefore the trace norm."))));

    private static DocumentBlock Thm(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Def(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("finite-sign-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
