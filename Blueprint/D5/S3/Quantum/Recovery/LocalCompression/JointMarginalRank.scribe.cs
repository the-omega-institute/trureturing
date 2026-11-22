using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class JointMarginalRankDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef ReebWolf =
        LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved");
    private static readonly LibraryNoteRef Fan =
        LibraryNoteRef.Create("D5/L/Eigenstructure/fan1949weyl");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum marginal rank is the ceiling of the joint rank divided by the traced dimension.",
        H("Marginal rank on a positive matrix's joint unitary orbit"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimum-joint-unitary-marginal-rank"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/LocalCompression/JointMarginalRank.minimum"),
            H("Exact least rank after discarding one factor"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(ReebWolf, Fan),
            Blocks(
                Paragraph(Text(
                    "For every positive semidefinite matrix on the product of spaces of dimensions "
                    + "m and e, with e positive, the least rank attainable by conjugating by a joint "
                    + "unitary and tracing out the second space is the ceiling of rank(X)/e. "
                    + "The statement includes zero matrices.")),
                Paragraph(Text(
                    "Diagonalize the retained marginal by a local unitary. Any zero diagonal "
                    + "entry is a sum of nonnegative joint diagonal entries, so all the joint "
                    + "entries above that coordinate vanish. Positivity then forces the corresponding "
                    + "joint rows to vanish. This bounds the joint rank by e times the marginal rank.")),
                Paragraph(Text(
                    "For attainment, use a joint eigenbasis and a permutation to put all "
                    + "nonzero eigenvalues in successive rows of the product basis. The number of "
                    + "occupied rows is the ceiling. Reeb and Wolf group eigenvalues into product "
                    + "rows in Section 3.3 after Proposition 5. Fan's variational principle gives "
                    + "the spectral bound underlying the rank obstruction."))),
            DescribeRole.Theorem))));
}
