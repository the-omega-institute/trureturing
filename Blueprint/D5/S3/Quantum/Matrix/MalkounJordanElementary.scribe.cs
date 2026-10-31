using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MalkounJordanElementaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/MalkounJordanElementary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/malkoun2026mo512579");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary symmetric eigenvalue inequality for a Hermitian Jordan product.",
        H("Malkoun's two-matrix elementary symmetric inequality"),
        Blocks(
            Node("elementarySymmetric", "The elementary symmetric polynomial",
                "The kth elementary symmetric polynomial is the sum of products over all k-element subsets of Fin n. "
                + "The entries are real; repeated values occupy distinct indices and retain their multiplicity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete source assertion",
                "MathOverflow 512579, revision 1, displayed first question (unpaginated): for every positive n, "
                + "every pair of complex n-by-n Hermitian positive semidefinite matrices X,Y, and every 1 ≤ k ≤ n, "
                + "the kth elementary symmetric polynomial of the eigenvalues of XY+YX is at most that of X²+Y². "
                + "Matrix.IsHermitian.eigenvalues lists the real eigenvalues with algebraic multiplicity, as certified by "
                + "Mathlib's roots_charpoly_eq_eigenvalues. The positivity hypotheses concern X and Y. "
                + "No positivity, invertibility, rank, simplicity of spectrum or small-order condition is imposed on XY+YX. "
                + "The unspecified subsequent promotion question is outside this assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The elementary symmetric inequality",
                "Fix a principal column set S. Stack the selected columns of X above those of Y to obtain U, "
                + "and reverse the two blocks to obtain V. Hermiticity gives U*U=V*V=(X²+Y²)[S,S] "
                + "and U*V=(XY+YX)[S,S]. The public frozen cauchyBinet declaration expands each determinant "
                + "over the same ordered row subsets. Writing u and v for the resulting minor determinants, "
                + "the real part of conjugate(u)v is at most half the sum of their squared moduli. "
                + "Summing and using the equal Gram matrices proves the inequality of the real principal determinants. "
                + "The characteristic-polynomial principal-minor identity and Hermitian spectral factorization identify "
                + "the sum of these determinants with the original elementary symmetric polynomial. "
                + "Summing the principal-minor inequalities proves the complete source assertion. "
                + "All determinant identities are polynomial, so zero and singular matrices remain in scope. "
                + "This is an application of existing Cauchy–Binet and spectral identities; no worldwide priority is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("malkoun-jordan-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
