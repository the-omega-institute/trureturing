using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveSmoothGridDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothGrid.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite grids of smoothed sieve weights",
        H("Finite grids of smoothed sieve weights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-moment-div-scale"),
                DeclarationHandle.Create(Prefix + "sieve_moment_div_scale"),
                H("Scaling product moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Dividing each of k residue functions by c divides their product moment by c to the kth power. The formula applies to both sharp and smooth normalized variables in integer recovery."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-defect-div-scale"),
                DeclarationHandle.Create(Prefix + "sieve_defect_div_scale"),
                H("Scaling the fourth Wick defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Dividing four residue functions by c divides their fourth moment and each of the three covariance products by c to the fourth power, and therefore scales their Wick defect by the same factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-grid-smoothed-third"),
                DeclarationHandle.Create(Prefix + "sieve_grid_smoothed_third"),
                H("Vanishing cubic moments on a fixed grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume KuperbergSmoothed. Fix a positive mesh, a bounded endpoint window and a density bound B. The normalized third moments of all admissible grid interval triples tend uniformly to zero over squarefree moduli with density at most B log h. Each tuple first supplies its own constant, with h and the modulus quantified afterwards. There are only finitely many tuples; intersecting their eventual sets takes a common threshold, equivalently their finite maximum. No weight depends on h. Dividing the cubic bound by (h log h) to the power three halves leaves a fixed multiple of h to the power minus one twenty-first times log h to the eighth power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-grid-smoothed-fourth"),
                DeclarationHandle.Create(Prefix + "sieve_grid_smoothed_fourth"),
                H("Vanishing fourth Wick defects on a fixed grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under KuperbergSmoothed, the normalized fourth Wick defects of all admissible grid interval quadruples tend uniformly to zero over squarefree moduli with density at most B log h. The mesh is fixed before applying the hypothesis to each tuple and taking the maximum of finitely many thresholds. The normalized error is bounded by a fixed multiple of h to the power minus one twenty-eighth times log h to the sixteenth power. KuperbergSmoothed is an explicit premise in finite-sieve expectation coordinates; no implication from a Ramanujan or Fourier formulation is asserted."))),
                DescribeRole.Theorem))));
}
