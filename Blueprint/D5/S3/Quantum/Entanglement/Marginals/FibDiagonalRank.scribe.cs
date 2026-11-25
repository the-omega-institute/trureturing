using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibDiagonalRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Gaussian norm equations for rational rank two with diagonal edge blocks.",
        H("Rational rank two for diagonal Fibonacci marginals"),
        Blocks(Describe.Lean(DescribeId.Create("fib-diagonal-rank"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/Marginals/FibDiagonalRank.rational_rank_le_two_diagonal_iff"),
            H("The coupling norm and the determinant norm"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let b be a positive rational middle occupation and put t = 1 − b. "
                    + "Set the observed couplings to zero and take diagonal endpoint blocks "
                    + "with entries (l, t − l) and (r, t − r), where l and r are distinct "
                    + "nonnegative rationals. There is a trace-one positive semidefinite "
                    + "joint extension with rational coordinates and rank at most two "
                    + "exactly when b(t − l − r) and lr are both Gaussian norms.")),
                Paragraph(Text(
                    "For coupling z, Schur elimination subtracts |z|²/b from the occupied "
                    + "entry of each block. The difference of the two residual determinants "
                    + "is (l − r)(t − l − r − |z|²/b). Equality fixes |z|² and leaves the "
                    + "two nonnegative diagonal residuals (l, r) and (r, l). Their common "
                    + "determinant is lr, which is the second norm in the fixed-coupling "
                    + "criterion."))),
            DescribeRole.Theorem))));
}
