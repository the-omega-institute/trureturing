using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful four-level example with a corner in its asymptotic overlap.",
        H("Failure of differentiability"), Blocks(
            Describe.Lean(DescribeId.Create("group-invariant-psi-explicit-function"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Result.counterexamplePsi"),
                H("Two competing overlap branches"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Set p=(16,9,4,1)/30 and q=(4,1,9,16)/30. Let C(s) be the sum of p(i) to the power s times q(i) to the power one minus s. The two-element group exchanges the first two and the last two coordinates, and its other relative overlap is C(1-s). The asymptotic function is the maximum of log C(s) and log C(1-s). All four entries of both probability vectors are strictly positive."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("group-invariant-psi-one-sided-derivatives"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Result.one_sided_derivs"),
                H("Distinct derivatives at the common value"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At s=1/2 the two overlaps both equal 7/10. Their logarithmic derivatives are opposite, with absolute value (2/7) log(4/3). The left difference quotients of their maximum converge to the negative value and the right difference quotients converge to the positive value. At a common value, division by a negative increment exchanges maximum with minimum; division by a positive increment preserves maximum. This gives the two limits directly from the branch derivatives."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-invariant-psi-refutation"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/GroupInvariantPsi/Result.result"),
                H("The differentiability assertion is false"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use diagonal density matrices with diagonals p and q on four complex dimensions and the permutation representation of the two-element group. The matrices are positive definite and have trace one. The tensor mixture sandwich proves convergence throughout the interval (0,1) and identifies its selected limit with the two-branch maximum. Differentiability at one half would make the left and right difference quotients converge to the same number, contradicting the two distinct limits. Finite groups are compact with uniform normalized Haar measure, so this example also refutes the corresponding assertion over compact groups. The proof uses this single explicit instance; it does not require a parameterized family."))), DescribeRole.Theorem))));
}
