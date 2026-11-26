using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class ComplexLocalTomographyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/ComplexLocalTomography.";
    private const string Literature = "D5/L/LieTheory/allanach2020anomalies";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Self-adjoint coordinates, real density matrices and complex product observables.",
        H("Local tomography and real division algebras"),
        Blocks(
            Paragraph(Text("A real diagonal coefficient determines each diagonal entry. A scalar "
                + "coefficient determines each strictly upper entry, and its adjoint determines "
                + "the reflected lower entry. This yields explicit real bases by placing the "
                + "scalar basis elements at those upper entries.")),
            Result("real-dimension", "finrank_realHermitian", "Real symmetric dimension",
                "There is one real coordinate per upper entry and per diagonal entry. The "
                + "real dimension of the symmetric matrices of size n is n(n + 1)/2."),
            Result("complex-dimension", "finrank_complexHermitian", "Complex Hermitian dimension",
                "Each strict upper entry has two real coordinates, in the scalar basis 1 and i. "
                + "Including the diagonal, the real dimension is n squared."),
            Result("quaternion-dimension", "finrank_quaternionHermitian", "Quaternionic Hermitian dimension",
                "Each strict upper entry has four real coordinates, in the scalar basis 1, i, j "
                + "and k. Including the diagonal, the real dimension is n(2n − 1)."),
            Result("division-algebra-selection", "division_algebra_local_tomography_selection",
                "Dimension multiplicativity",
                "For both local sizes at least two, the real symmetric composite dimension exceeds "
                + "the product of the local dimensions. The complex Hermitian dimensions multiply "
                + "exactly, and the quaternionic Hermitian composite dimension is strictly smaller "
                + "than the product of the local dimensions. Thus complex scalars are the unique "
                + "choice among these three for dimension multiplicativity."),
            Result("complex-tensor-basis", "tensorHermBasis_apply", "Explicit complex tensor basis",
                "The basis vector indexed by a pair of local indices is the Kronecker product of "
                + "the corresponding local Hermitian basis vectors."),
            Result("complex-span", "span_tensor_hermitian", "Complex local tomography",
                "The real span of all Kronecker products of local Hermitian matrices is the "
                + "whole Hermitian space on the product index set."),
            Result("real-symmetry", "W_symmetric", "A symmetric tensor of two skew directions",
                "The real matrix J has zero diagonal and off-diagonal entries 1 and −1. "
                + "Its Kronecker square W is symmetric, since transposition negates both factors."),
            Result("real-trace", "blind_spot_trace", "Trace orthogonality",
                "Every Kronecker product of two real symmetric two-by-two matrices has zero "
                + "trace pairing with W. The pairing factors into local trace pairings with J."),
            Result("real-density", "real_density_blind_spot", "Indistinguishable real density matrices",
                "The two matrices I/4 + W/16 and I/4 − W/16 are distinct, strictly positive "
                + "definite and have trace one. Every product of local real symmetric observables "
                + "has the same trace pairing with both matrices."))));

    private static DocumentBlock Result(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Literature)),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
