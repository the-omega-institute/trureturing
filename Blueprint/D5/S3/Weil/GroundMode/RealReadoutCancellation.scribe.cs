using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GroundMode;

internal sealed class RealReadoutCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate source; Lean elaboration and Scribe emission are not claimed.",
        H("RealReadoutCancellation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-pairGramDet"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.pairGramDet"),
                H("pairGramDet"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual real Gram determinant of the two representers. Its strict positivity is a stated rank-two hypothesis for the inverse-based results."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-pairEnergy"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.pairEnergy"),
                H("pairEnergy"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit quadratic minimum-energy expression. Its use at rank two is proved below; no positive-definiteness or inverse is supplied by a numeric label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-pairWitness"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.pairWitness"),
                H("pairWitness"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real linear combination of the two actual representers using the scalar inverse Gram coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-pairWitness-spec"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.pairWitness_spec"),
                H("pairWitness spec"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compute both constraints directly and calculate the squared norm from the same two constraints. This is an explicit attaining witness in the actual real Hilbert space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-real-pair-energy-decomposition"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.real_pair_energy_decomposition"),
                H("real pair energy decomposition"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every feasible error differs from the constructed witness by a vector orthogonal to both representers. The exact Pythagorean identity proves minimum energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-real-pair-attainable-iff"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.real_pair_attainable_iff"),
                H("real pair attainable iff"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Necessity follows from the nonnegative residual energy. Sufficiency uses the constructed witness. Negative error budgets are also handled by the equivalence. Rank-deficient Gram data are not silently inverted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-pairWitness-orthogonal"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.pairWitness_orthogonal"),
                H("pairWitness orthogonal"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witness is a linear combination of candidate-orthogonal representers. It belongs to the same error subspace, so the minimum does not exploit a forbidden candidate direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-real-ball-complex-readout-ne-zero"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.real_ball_complex_readout_ne_zero"),
                H("real ball complex readout ne zero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A complex zero requires both real readout equations for one real error. If its exact minimum energy exceeds the error budget, no such error exists. Exactness is over the real ball, not over the eigenvectors of a prescribed operator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-dual-pair-exclusion"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.dual_pair_exclusion"),
                H("dual pair exclusion"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any real linear combination of the two target equations supplies a Cauchy-Schwarz separation certificate. No Gram rank or inverse is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realreadoutcancellation-rescaled-pair-cost"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealReadoutCancellation.rescaled_pair_cost"),
                H("rescaled pair cost"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cancel the nonzero squared scaling of numerator and denominator. For nonreal Fourier evaluation one may divide the imaginary equation by its nonzero ordinate and then study the limiting transverse kernel separately."))),
                DescribeRole.Theorem))));
}
