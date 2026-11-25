using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdCoverVirasoroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverVirasoro.";
    private static readonly LibraryNoteRef FockSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/kytola2025virasoro");
    private static readonly LibraryNoteRef TwistedCurrents =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-three covering operators and fractional current brackets on the full rank-one polynomial Fock space.",
        H("Third-Cover Virasoro Modes and Fractional Currents"),
        Blocks(
            Paragraph(Text("All products are compositions of complex-linear endomorphisms of the full rank-one Fock "
                + "space, the algebra of polynomials in countably many variables. The integer current and pointwise "
                + "finite normal-ordered Sugawara operator are mode and L from PolynomialFockSugawaraSupport. "
                + "There is no bound on the polynomial degree or its variable indices.")),
            Describe.Lean(
                DescribeId.Create("third-cover-mode"),
                DeclarationHandle.Create(Prefix + "coverMode"),
                H("Covering Virasoro mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(FockSource),
                Blocks(Paragraph(Text("For each integer m, the covering mode L3(m) is L(3m)/3 plus "
                    + "the identity divided by nine when m=0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-cover-current"),
                DeclarationHandle.Create(Prefix + "current"),
                H("Current at frequency r/3"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCurrents),
                Blocks(Paragraph(Text("For any complex scale a and integer r, J_a(r) is a times mode(r). "
                    + "Its frequency is r/3. The two nonintegral grids are Z+1/3 and Z+2/3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-cover-virasoro-bracket"),
                DeclarationHandle.Create(Prefix + "coverMode_commutator"),
                H("Virasoro commutator at central charge three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(FockSource),
                Blocks(Paragraph(Text("For all integers n and m, [L3(n), L3(m)] is (n-m)L3(n+m) plus "
                    + "3(n^3-n)/12 times the identity when n+m=0. The scalar shifts commute. "
                    + "Using PolynomialFockVirasoroCentral.L_commutator at 3n and 3m gives the central "
                    + "polynomial ((3n)^3-3n)/108. When m=-n, the contribution (n-m)/9 from the "
                    + "shifted output mode leaves 3(n^3-n)/12."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-current-bracket"),
                DeclarationHandle.Create(Prefix + "current_commutator"),
                H("Normalized current bracket and complementary grid support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCurrents),
                Blocks(Paragraph(Text("For every complex a with a^2=1/3 and all integers r and s, "
                    + "[J_a(r), J_a(s)] equals (r/3) times the identity when r+s=0 and is zero otherwise. "
                    + "If r has nonzero residue modulo three, the bracket is nonzero exactly when r+s=0 "
                    + "and the nonnegative residues of r and s sum to three. The factor a^2 rescales "
                    + "PolynomialFockSugawaraCommutators.mode_heisenberg, and the coefficient r/3 is "
                    + "nonzero for a fractional frequency. This is the opposite-frequency pairing of "
                    + "Bakalov and Kac, arXiv:math/0402315v1, equation (4.23), with the paired form entry "
                    + "normalized to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-current-covariance"),
                DeclarationHandle.Create(Prefix + "coverMode_current_commutator"),
                H("Covering modes preserve each current grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCurrents),
                Blocks(Paragraph(Text("For every complex a and all integers m and r, [L3(m), J_a(r)] "
                    + "equals -(r/3) J_a(3m+r), and 3m+r and r have the same residue modulo three. "
                    + "The operator identity uses PolynomialFockSugawaraCommutators.L_mode_commutator "
                    + "and the scalar zero-mode shift commutes with every current. If a^2=1/3 and r has "
                    + "nonzero residue, the mixed bracket is nonzero. The shifted current has a nonzero "
                    + "bracket with its opposite-frequency current, so the shifted current itself is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-cover-first-vacuum-descendant"),
                DeclarationHandle.Create(Prefix + "coverMode_first_vacuum_descendant"),
                H("The first covering vacuum descendant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(FockSource),
                Blocks(Paragraph(Text("On the constant vacuum 1, L3(1)L3(-1) returns (2/9) times 1. "
                    + "PolynomialFockLZeroSpectrum.lZero_spectrum puts the constant monomial in the "
                    + "native L(0) zero eigenspace. The support bound for L(3) on 1 is the open integer "
                    + "interval (1,2), so L3(1) kills 1. The covering commutator at 1 and -1 then "
                    + "reduces the composition to twice the shifted L3(0) on 1."))),
                DescribeRole.Theorem),
            Paragraph(Text("The oscillator pairing is relevant to the sixteen complementary eigenspace pairs in "
                + "the P48q order-three anomaly calculation for the central-charge-48 extremal VOA problem. "
                + "The covering calculation here includes the integral grid alongside both fractional grids. "
                + "The separation of its full Virasoro action into the integral-grid and complementary-grid "
                + "actions is a separate factorization problem.")))));
}
