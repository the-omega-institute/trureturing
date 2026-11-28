using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.SetImaginarity;

internal sealed class TraceWordDetectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/guopanwangdu2026setimaginarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every ordered trace word can be real even when four states have no common real basis.",
        H("A quaternionic obstruction to a common real basis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-word-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Real traces as a sufficiency condition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The assertion quantifies over every injective family of four positive "
                        + "semidefinite trace-one complex matrices, with rows and columns indexed "
                        + "by the disjoint union of two copies of Fin 2. It says that if every "
                        + "ordered trace word has imaginary part zero, for every natural length "
                        + "and every choice of letters, then one unitary makes all four states "
                        + "entrywise real. The introduction and Appendix C suggest a detection "
                        + "criterion whose sufficiency direction uses only the bounded window. "
                        + "Replacing that premise by reality of all trace words gives the "
                        + "separate implication tested here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-word-refutation"), DeclarationHandle.Create(Prefix + "result"),
                H("Four positive definite states refute sufficiency"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the Pauli matrices X, Y, Z, with the upper right entry of Y equal "
                            + "to minus i. In the ordered tensor basis, use the four Hermitian "
                            + "involutions Z tensor I, X tensor I, Y tensor X and Y tensor Z. "
                            + "For each such G take the state (2I + G)/8. Their entries "
                            + "distinguish them, and their traces are one because each G is "
                            + "traceless. Each state is I/8 plus the Gram matrix of I + G "
                            + "scaled by 1/16, hence is positive definite.")),
                    Paragraph(Text(
                        "Let J have rows (0, 1) and (-1, 0), and let Q be block diagonal with "
                            + "two copies of J. Each state intertwines its entrywise conjugate "
                            + "via Q. Induction on ordered words preserves the intertwining "
                            + "equation. Since the inverse of Q is minus Q, cyclicity of trace "
                            + "then shows every word has trace equal to its complex conjugate.")),
                    Paragraph(Text(
                        "If a unitary U made all four states real, the product of its adjoint "
                            + "with its entrywise conjugate would be a symmetric unitary C "
                            + "intertwining all four generators with their conjugates. "
                            + "The first generator forces both off-diagonal blocks of C to vanish. "
                            + "The second forces the diagonal blocks to be equal. The third and "
                            + "fourth force their common block to anticommute with X and Z. "
                            + "Anticommutation with Z gives zero diagonal entries, and "
                            + "anticommutation with X gives opposite off-diagonal entries. "
                            + "Thus C is a scalar multiple of Q, which is skew-symmetric. "
                            + "Symmetry then forces C to vanish, contradicting unitarity.")),
                    Paragraph(Text(
                        "All words in the dimension-four window from three to ten have real "
                            + "trace, so the same family refutes the inferred bounded "
                            + "sufficiency direction. Any restriction to words with distinct "
                            + "letters also retains this counterexample. The earlier work of "
                            + "Miyazaki and Matsumoto on antiunitary symmetries is related "
                            + "literature."))),
                DescribeRole.Theorem))));
}
