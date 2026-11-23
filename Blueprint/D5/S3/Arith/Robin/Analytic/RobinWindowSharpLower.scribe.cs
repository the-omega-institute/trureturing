using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class RobinWindowSharpLowerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Robin/Analytic/RobinWindowSharpLower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp lower power bounds for Robin window mass",
        H("Actual zero strips and weighted negative mass"),
        Blocks(
            Paragraph(Text("Write M_b(Y) for the actual weighted negative mass from Y to Y^b "
                + "of the Chebyshev kernel (ψ(t)−t)/t². A strip of width α>0 means that every "
                + "nontrivial zeta zero has real part at most 1−α.")),
            Describe.Lean(DescribeId.Create("fixed-power-mass-lower"),
                DeclarationHandle.Create(Module + "off_line_zero_forces_weighted_negative_mass_of_actual_strip"),
                H("A fixed zero on an inner power window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix 1<d<b and a nontrivial zero with real part β>1/2. "
                    + "If max(r,d/2−bα,0)<d(β−1/2), then Y^r≤M_b(Y) for every sufficiently "
                    + "large real Y. Choose an intermediate power s between these bounds. "
                    + "The inner prime mass is at least Y^s. Its comparison with the full mass "
                    + "has a bounded coefficient on M_b(Y), an endpoint term of power d/2−bα, "
                    + "and a logarithmic prime-power correction. The last two terms are absorbed "
                    + "by Y^s, which also dominates the target power."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-abscissa-power-criterion"),
                DeclarationHandle.Create(Module + "weighted_negative_mass_power_criterion"),
                H("The zero abscissa and cofinal power bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let β* be the supremum of the real parts of the nontrivial zeros. "
                    + "Under a positive strip and for fixed b>1, each real 0<r<b(β*−1/2) satisfies "
                    + "Y^r≤M_b(Y) eventually. Use the positive strip width 1−β*, choose d<b "
                    + "with r<d(β*−1/2), and take an actual zero sufficiently near β*. "
                    + "The gap at the supremum between the inner pole power and the endpoint power "
                    + "is (b−d)(1−β*)>0. For a fixed p≥0 and constant C, a cofinal bound "
                    + "M_b(Y)≤CY^p then forces β*≤1/2+p/b."))),
                DescribeRole.Theorem))));
}
