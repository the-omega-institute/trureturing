using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ChenChenBoundaryStepsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ChenChenBoundarySteps.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026chenchenparity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The row polynomials of the step-m Eulerian triangle factor explicitly at m = −1, −2 and "
            + "0, their roots at m = −1, −2 lie on the unit circle, and row six at m = −3 has a "
            + "nonreal root.",
        H("Row polynomials at boundary steps"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-chen-row-poly-recursion"),
                DeclarationHandle.Create(Prefix + "rowPoly_succ"),
                H("Polynomial form of the recursion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every solution T of the step-m recursion and every n ≥ 1, the row "
                    + "polynomial R_n(X) = ∑ T(n,k) X^(k−1) satisfies R_{n+1} = (1 + "
                    + "(m(n−1)+1)X) R_n + m X (1 − X) R_n′. Comparing the coefficient of X^j on "
                    + "both sides gives (mj+1)T(n,j+1) + (m(n−j)+1)T(n,j), which is the "
                    + "recursion for T(n+1,j+1) with zero padding outside 1 ≤ k ≤ n. This is "
                    + "identity (5) of H. Ma and W. Zhang's paper."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("chen-chen-boundary-steps-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Factorizations at boundary steps"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For q ≥ 1 and every complex y, R_{−1,2q}(y) = R_{−2,2q}(y) = (1 − "
                    + "y)^(2q−2)(1 + y), R_{−1,2q+1}(y) = (1 − y)^(2q−2)(1 + y²) and "
                    + "R_{−2,2q+1}(y) = (1 − y)^(2q). Hence for n ≥ 2 every root of R_{−1,n} and "
                    + "R_{−2,n} has modulus 1, and some root does, so the largest root modulus is "
                    + "1. Also R_{0,n}(y) = (1 + y)^(n−1) for n ≥ 1, and R_{−3,6}(y) = (1 + y)(y⁴ "
                    + "+ 16y³ + 246y² + 16y + 1) has a nonreal root, since the quartic is "
                    + "positive on the real line. The factorizations follow from the polynomial "
                    + "recursion in even–odd pairs. These are the clauses of Corollary 8 of H. Ma "
                    + "and W. Zhang's proof of Chen and Chen's parity-positivity conjectures (DOI "
                    + "10.5281/zenodo.23957560) other than real-rootedness for m > 0, which is "
                    + "not formalized here."))),
                DescribeRole.Theorem))));
}
