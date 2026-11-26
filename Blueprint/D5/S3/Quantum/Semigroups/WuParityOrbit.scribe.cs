using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuParityOrbitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuParityOrbit.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-mode cubic deficit on physical parity blocks is a weighted average of four diagonal deficits.",
        H("Parity reduction of Wu’s cubic inequality"),
        Blocks(
            Describe.Lean(DescribeId.Create("cubic-deficit-parity-orbit"),
                DeclarationHandle.Create(Owner + "cubicDeficit_parity_orbit"),
                H("Cubic deficit on a parity orbit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("In occupation order (00, 01, 10, 11), put Hermitian blocks A and B on the " +
                        "ordered sectors (00, 11) and (01, 10). Let v and w be their eigenvalues in the orders " +
                        "given by their unitary eigenframes, and let p and q be the squared moduli of the " +
                        "respective (0, 1) entries. The cubic deficit uses the real logarithm in its trace expression, " +
                        "which is the Gibbs entropy term on positive semidefinite inputs. For any r ≥ 1 and c ∈ ℝ, " +
                        "the deficit equals the weighted sum of the deficits on " +
                        "the four physical diagonal assignments of v and w. The weights for swapping neither " +
                        "block, B alone, A alone, or both are (1 − p)(1 − q), (1 − p)q, p(1 − q), and pq.")),
                    Paragraph(Text("With matrix units indexed from zero, the lowering jumps are E₀₂ + E₁₃ and " +
                        "−E₀₁ + E₂₃. The interference terms vanish on parity blocks. Each surviving mixed " +
                        "product uses one diagonal moment from each block, so independent swaps reproduce it " +
                        "in expectation. The anticommutator and log D terms use single diagonal moments. " +
                        "The trace of M³ log M³ and the total cubic mass depend only on the eigenvalues."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cubic-inequality-of-commute-parity"),
                DeclarationHandle.Create(Owner + "cubic_inequality_of_commute_parity"),
                H("Cubic inequality for parity-preserving observables"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("In Wu v1, Remark 3.15, eqs. (3.54)–(3.55), take exponent three and two signed " +
                        "CAR modes with the same Gibbs odds r³, where r = exp(β/3) ≥ 1. Let X be positive " +
                        "semidefinite and commute with diag(1, −1, −1, 1). Set M = G X G with G = D^(1/6) " +
                        "for the product Gibbs density D. With ordinary trace, the signed Dirichlet term " +
                        "(9/8) Re Tr(M² G ℒᵣ(X) G) bounds α(r)[Re Tr(M³(log M³ − log D)) − t log t], " +
                        "where t = Re Tr(M³) and α(1) = 1/2. The matrix logarithms use the real functional " +
                        "calculus with Real.log 0 = 0.")),
                    Paragraph(Text("The diagonal Gibbs factor preserves the parity blocks of X. Each of the four " +
                        "diagonal assignments of the block spectra of M satisfies the occupation-conditioned " +
                        "cubic bound. The orbit identity averages these endpoint bounds, including for singular blocks."))),
                DescribeRole.Theorem))));
}
