using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdCoverGroundSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverGroundSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complementary zero mode has point spectrum 1/9+n/3 for natural n and a one-dimensional ground eigenspace of weight 1/9.",
        H("The Fractional Zero-Mode Spectrum"),
        Blocks(
            Paragraph(Text("Use the actual fractionalVirasoro(0) on ComplementFock. The ordinary vacuum slice Q maps to join(1 "
                + "tensor Q), which is the polynomial renaming into the native Fock space. The split operator identity "
                + "and the native PolynomialFockLZeroSpectrum.lZero_spectrum give the zero-mode action on this slice. The "
                + "proof below uses these repository results and coefficient uniqueness, with the merged cover shift "
                + "fixed at 1/9.")),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-occupation-energy"),
                DeclarationHandle.Create(Prefix + "occupationEnergy"),
                H("Native occupation weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finitely supported occupation vector d on the complementary variable type, sum (k.val+1) d(k) "
                           + "over its support. Divide this natural number by three to obtain the excitation contribution to the "
                           + "complementary weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-occupation-energy-eq-zero-iff"),
                DeclarationHandle.Create(Prefix + "occupationEnergy_eq_zero_iff"),
                H("Zero occupation energy detects the vacuum occupation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Identify occupationEnergy with the Finsupp weight for the positive natural weights k.val+1. "
                           + "Finsupp.weight_eq_zero_iff_eq_zero then gives exactly the zero occupation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-fractional-virasoro-zero-monomial"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_zero_monomial"),
                H("Diagonal action on every monomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every occupation d and complex coefficient a, fractionalVirasoro(0)(monomial(d,a)) equals "
                           + "(1/9+occupationEnergy(d)/3) times that monomial. The ordinary factor has zero native energy on 1. The "
                           + "variable renaming is injective, and summing native energy after the exponent pushforward gives exactly "
                           + "occupationEnergy(d)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-fractional-virasoro-zero-coeff"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_zero_coeff"),
                H("Diagonal action on arbitrary polynomial coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient at d of the image of any polynomial Q equals (1/9+occupationEnergy(d)/3) times the "
                           + "coefficient at d of Q. Expand Q into its finite monomial support and use the diagonal formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-fractional-virasoro-zero-ground-eigenspace"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_zero_ground_eigenspace"),
                H("The ground eigenspace is the vacuum line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel of fractionalVirasoro(0) minus 1/9 times the identity is exactly the complex span of the "
                           + "constant polynomial 1. A nonzero coefficient of any vector in this kernel must have energy zero, so "
                           + "its support lies in the zero occupation. ThirdCoverComplement.fractionalVirasoro_vacuum supplies "
                           + "the reverse inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-fractional-virasoro-zero-eigenvalue"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_zero_eigenvalue"),
                H("Exact point spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists a nonzero Q with fractionalVirasoro(0)(Q)=a Q exactly when a=1/9+n/3 for some "
                           + "natural n. A nonzero coefficient forces the stated form. Conversely the coefficient-one monomial "
                           + "with exponent n at complementary label 0 has occupation energy n and realizes that eigenvalue."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-fractional-virasoro-zero-eigenvalue-lower-bound"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_zero_eigenvalue_lower_bound"),
                H("Lower bound on eigenvalues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonzero-state complex eigenvalue has real part at least 1/9 because its excitation shift is a "
                           + "natural number divided by three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thirdcovergroundspectrum-fractional-virasoro-zero-minimum"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_zero_minimum"),
                H("The vacuum attains the minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Among real numbers x admitting a nonzero polynomial Q with fractionalVirasoro(0)(Q)=x Q, 1/9 is least. "
                           + "The constant polynomial is a nonzero witness to attainment, and the real-part lower bound applies to "
                           + "every such x."))),
                DescribeRole.Theorem),
            Paragraph(Text("These statements establish all monomial weights, the exact shifted nonnegative point spectrum, "
                + "and the exact lowest eigenspace of the one-pair polynomial complementary factor. "
                + "The full lattice twisted-module spectrum requires further constructions.")))));
}
