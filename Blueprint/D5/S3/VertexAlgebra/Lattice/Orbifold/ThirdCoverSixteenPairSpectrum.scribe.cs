using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdCoverSixteenPairSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum.";
    private static readonly LibraryNoteRef TwistedCurrents =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of the sixteen moving oscillator zero modes has point spectrum 16/9+n/3 for natural n "
        + "and a one-dimensional ground eigenspace.",
        H("The Sixteen-Pair Oscillator Zero Mode"),
        Blocks(
            Paragraph(Text("The moving polynomial space has one factor for each of the sixteen complementary pairs "
                + "used in the order-three P48q calculation. Each factor has the two nonzero residue grids, "
                + "with native frequency k.val+1 and fractional frequency (k.val+1)/3. The pairing of opposite "
                + "frequencies is that of Bakalov and Kac, arXiv:math/0402315v1, equation (4.23), as used in "
                + "ThirdCoverComplement.")),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-pair-lzero"),
                DeclarationHandle.Create(Prefix + "pairLZero"),
                H("The zero mode on one selected factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCurrents),
                Blocks(Paragraph(Text("Split each basis monomial into its selected pair and the remaining variables. "
                    + "Apply ThirdCoverComplement.fractionalVirasoro(0) to the selected part, rename its variables "
                    + "back into the full space, and multiply by the remaining monomial. Extend linearly."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-pair-lzero-separated"),
                DeclarationHandle.Create(Prefix + "pairLZero_separated"),
                H("The other factors carry the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the product of arbitrary polynomials in the selected and remaining "
                    + "variables, the operator applies the one-pair zero mode to the selected polynomial and "
                    + "leaves the remaining polynomial as the second factor. Restriction of occupations gives "
                    + "the identity on pairs of monomials, and bilinearity extends it to all such products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-fractional-lzero"),
                DeclarationHandle.Create(Prefix + "fractionalLZero"),
                H("The sum of the sixteen lifted operators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum pairLZero over Fin 16. This is the moving oscillator operator "
                    + "on the full polynomial space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-occupation-energy"),
                DeclarationHandle.Create(Prefix + "totalOccupationEnergy"),
                H("Total native occupation energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each occupied variable (i,k), sum its exponent times k.val+1. "
                    + "Summing the sixteen pair energies gives this total by currying the occupation vector. "
                    + "All variable frequencies are positive, so the total vanishes exactly at zero occupation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-lzero-monomial"),
                DeclarationHandle.Create(Prefix + "fractionalLZero_monomial"),
                H("The weight of each occupation monomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PolynomialFockLZeroSpectrum.lZero_spectrum computes the native oscillator "
                    + "energy by the creation commutator and the vacuum action. On the ordinary vacuum slice "
                    + "of the cover splitting, ThirdCoverGroundSpectrum.fractionalVirasoro_zero_monomial "
                    + "gives a shift of 1/9 and one third of the pair occupation energy. The sixteen terms "
                    + "sum to 16/9 plus one third of the total occupation energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-lzero-coeff"),
                DeclarationHandle.Create(Prefix + "fractionalLZero_coeff"),
                H("Coefficientwise action on any polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expanding a polynomial over its finite support shows that the coefficient "
                    + "of each occupation is multiplied by the weight of that occupation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-exact-point-spectrum"),
                DeclarationHandle.Create(Prefix + "fractionalLZero_eigenvalue_iff"),
                H("Exact point spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero coefficient of an eigenvector forces its eigenvalue to equal "
                    + "16/9+n/3 for that coefficient's natural occupation energy n. Conversely, put exponent n "
                    + "at the variable in pair zero with complement label zero and put exponent zero elsewhere. "
                    + "That variable has native frequency one, so the coefficient-one monomial has energy n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-ground-eigenspace"),
                DeclarationHandle.Create(Prefix + "fractionalLZero_ground_eigenspace"),
                H("The vacuum line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An eigenvector at 16/9 can only have a nonzero coefficient at zero "
                    + "occupation. The constant polynomial 1 has that weight, so the eigenspace is its complex span."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-ground-finrank"),
                DeclarationHandle.Create(Prefix + "fractionalLZero_ground_finrank"),
                H("Ground multiplicity one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The span of the nonzero vacuum polynomial has complex dimension one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-sixteen-minimum"),
                DeclarationHandle.Create(Prefix + "fractionalLZero_minimum"),
                H("Minimum real eigenvalue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every real eigenvalue is at least 16/9 since n is natural, and the "
                    + "vacuum attains 16/9."))),
                DescribeRole.Theorem))));
}
