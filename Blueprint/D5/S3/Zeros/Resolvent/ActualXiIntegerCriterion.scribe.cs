using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiIntegerCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual xi integer Hankel criterion",
        H("Actual xi integer Hankel criterion"),
        Blocks(Describe.Lean(
                DescribeId.Create("actual-xi-integer-negative-of-not-rh"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiIntegerCriterion.actual_xi_integer_negative_of_not_rh"),
                H("Every failure of RH has a finite integer negative direction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every proof that Mathlib RiemannHypothesis is false, there exist a natural N and integer vector u on Fin(N+1) such that the sum over a and b in Fin(N+1) of u(a) u(b) times xiCoefficient(a+b), with integer coefficients cast to the reals, is strictly negative. The xiCoefficient is the existing actual xiOdd derivative coefficient of order 2j+1 divided by its factorial, followed by real part. No nonreal-node existence premise is added to this statement.")),
                    Paragraph(Text("Failure of the actual nontrivial-zero critical-line equivalence supplies an enumerated zero off the line. Its height is nonzero by the existing actual height exclusion; if negative, original zero conjugation gives a positive-height representative with the same real part. The folded node reality equivalence then gives a nonreal node. Nonzero weights follow from exact positive analytic multiplicity, nonzero gamma, and the existing denominator exclusion. Finite node superlevel cuts follow from actual spectral-ball finiteness. The generic complete-spectrum construction consumes these facts.")),
                    Paragraph(Text("The actual public Hankel identity is used at shift m=0: its square contains node to power m, and its coefficient index is 2m+a+b. This proves a negative direction for the unshifted all-degree criterion. Every original positive-height zero and every original analytic multiplicity remains in the complete sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-actual-xi-integer-hankel-nonnegative"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiIntegerCriterion.rh_iff_actual_xi_integer_hankel_nonnegative"),
                H("Standard RH equals the all-degree integer sign criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib RiemannHypothesis holds if and only if, for every natural N and every integer vector u on Fin(N+1), the real quadratic form with entries xiCoefficient(a+b) is nonnegative. RH implies this sign by the existing explicit-RH real-vector positivity theorem at m=0; failure of RH gives the finite integer negative direction above.")),
                    Paragraph(Text("This equivalence proves neither RH nor the universal nonnegativity assertion. Checking finitely many degrees is insufficient. The construction makes no Robin n greater than 5040 claim, no modulus-square replacement, no truncated-spectrum claim, no optimizer subsequence, and no literature novelty claim."))),
                DescribeRole.Theorem))));
}
