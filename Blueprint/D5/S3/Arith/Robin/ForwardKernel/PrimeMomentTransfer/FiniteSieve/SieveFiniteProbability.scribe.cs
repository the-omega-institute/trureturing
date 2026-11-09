using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveFiniteProbabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFiniteProbability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite residue expectations and fourth norms use the uniform probability measure.",
        H("Finite residue expectations and fourth norms use the uniform probability measure."),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-probability"),
                DeclarationHandle.Create(Prefix + "sieve_probability"),
                H("Uniform residue probability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalized counting measure on the residues modulo a positive integer has total mass one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-expectation-integral"),
                DeclarationHandle.Create(Prefix + "sieve_expectation_integral"),
                H("Uniform expectation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of a real residue function against normalized counting measure equals its finite sum divided by the modulus."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-mem-lp-four"),
                DeclarationHandle.Create(Prefix + "sieve_memLp_four"),
                H("Finite fourth moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every real function on the finite residue space belongs to L4 for the uniform probability measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-norm4-eq-lp-norm"),
                DeclarationHandle.Create(Prefix + "sieve_norm4_eq_lpNorm"),
                H("Fourth norm identification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth root of the expected fourth absolute power equals the real L4 norm under the uniform residue measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-norm4-nonneg"),
                DeclarationHandle.Create(Prefix + "sieve_norm4_nonneg"),
                H("Nonnegative fourth norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite fourth norm of every real residue function is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-norm4-fourth"),
                DeclarationHandle.Create(Prefix + "sieve_norm4_fourth"),
                H("Recovering the fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth power of the finite fourth norm equals the expected fourth absolute power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-norm4-add-le"),
                DeclarationHandle.Create(Prefix + "sieve_norm4_add_le"),
                H("Fourth norm triangle inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fourth norm of the sum of two real residue functions is at most the sum of their fourth norms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-norm4-smul"),
                DeclarationHandle.Create(Prefix + "sieve_norm4_smul"),
                H("Fourth norm homogeneity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by a real constant multiplies the finite fourth norm by the absolute value of that constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-interval-moment-eq-product-moment"),
                DeclarationHandle.Create(Prefix + "sieve_interval_moment_eq_product_moment"),
                H("Interval moment coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The interval sieve moment equals the expectation of the product of the corresponding interval sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-interval-defect-eq-wick-defect"),
                DeclarationHandle.Create(Prefix + "sieve_interval_defect_eq_wick_defect"),
                H("Interval pairing coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The interval Wick defect equals the fourth product moment minus its three covariance pairings in residue-function coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-scale-power"),
                DeclarationHandle.Create(Prefix + "sieve_scale_power"),
                H("Powers of the interval scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a length at least two, the square root of H log H is positive and its kth power equals (H log H) raised to k divided by two."))),
                DescribeRole.Theorem))));
}
