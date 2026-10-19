using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class UpperDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/Upper.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal square-root bounds for real symmetric zero-one matrices.",
        H("Universal Ky Fan upper bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ky-fan-truncation"),
                DeclarationHandle.Create(Owner + "kyFan_eq_of_ge"),
                H("Truncation at the matrix dimension"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular")),
                Blocks(Paragraph(Text("Every singular value with index at least the matrix dimension vanishes. Hence extending a Ky Fan prefix beyond that dimension does not change its sum. The cited source supplies the singular-value machinery."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ky-fan-zero-one-upper-bound"),
                DeclarationHandle.Create(Owner + "kyFan_le_of_zero_one"),
                H("Square-root upper bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/kitware2026rectangular"),
                    LibraryNoteRef.Create("D5/L/Eigenstructure/nikiforov2015extrema")),
                Blocks(Paragraph(Text("The rectangular source supplies the variational machinery. Nikiforov's bound (12) gives the known graph bound, where the adjacency matrix has zero diagonal. The centering argument here extends that bound to symmetric zero-one matrices with arbitrary diagonal. For a symmetric zero-one matrix A of order n, every Ky Fan prefix of length k is at most n times (1+sqrt(k))/2. Centering gives B=2A-J, with all entries of B equal to plus or minus one. An attaining signed orthonormal family pairs with B by at most sqrt(k) times n, using Cauchy-Schwarz and Bessel's inequality on the rows. Its pairing with J is at most n by Bessel's inequality on the constant vector. Summing these bounds proves the result; prefixes longer than n reduce by truncation. Diagonal entries equal to one are allowed."))),
                DescribeRole.Theorem))));
}
