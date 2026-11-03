using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiHankelDictionaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite real-polynomial Hankel identity for actual xi derivatives.",
        H("Finite real-polynomial Hankel identity for actual xi derivatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualxihankeldictionary"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiHankelDictionary.actual_xi_hankel_identity"),
                H("Finite real-polynomial Hankel identity for actual xi derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each natural j define xiCoefficient(j) as the real part of iteratedDeriv(2j+1, xiOdd)(0) divided by (2j+1) factorial. The preceding all-order dictionary identifies it with the real actual folded moment. For arbitrary natural N and m and real coefficients indexed by Fin(N+1), put p(z) equal to their finite power polynomial.")),
                    Paragraph(Text("The finite Hankel form sum over a,b of u(a) u(b) xiCoefficient(2m+a+b) equals the real part of the complete sum over actual positive-height zeros of weight times the complex square of node to power m times p(node). Finite distributivity and summable moment columns justify the equality and absolute convergence. The square is the complex algebraic square; it is never a squared norm.")),
                    Paragraph(Text("With Mathlib RiemannHypothesis explicitly assumed, every node and weight is positive real, so this same finite form is nonnegative. There is no unconditional positivity or RH theorem. An off-line quadruple folds to one nonreal conjugate pair of distinct nodes; analytic multiplicity changes weights, not pair counts. No folded or full-chain negative-index count is proved here. A spectral power factor imposes no physical-space atom moment condition.")))))));
}
