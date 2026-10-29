using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Algebraic Dual-Coset Point Spectrum",
        H("Actual Algebraic Dual-Coset Point Spectrum"),
        Blocks(
            Paragraph(Text("The spectrum is the algebraic point spectrum of the ACTUAL original-omega moduleL_0 on the full finite-support carrier. H is a two-sided inverse of the original complex Gram matrix; beta is integral; mu is rational and G_Q mu=beta. Positive original real Gram constructs a nonnegative attained minimum h and finite fibers. Every eigenvalue is h+n for a natural n. Equality with the full set h+N requires positive rank, where frequency-one oscillators realize every n. In rank zero the carrier is the existing nonzero vacuum line, the original omega is zero, the only eigenvalue is zero, and the constructed h is zero. Bottom fibers consist of all minimizing charges and zero oscillator exponent. For the rank-one even Gram [2] with mu=1/2, h=1/4 is attained at two distinct charges. Virasoro modes send energy e to e-m and positive modes annihilate the entire bottom space. No generation by Virasoro modes, analytic Hilbert spectrum, classification, fusion, complete CFT, Monster, string theory or AdS/CFT result is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-point-spectrum-subset"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.point_spectrum_subset"),
                H("point spectrum subset"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any nonzero actual eigenvector has a nonzero actual basis coefficient, which forces its COMPLEX eigenvalue to equal cast(h+n) for a natural n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-positive-rank-point-spectrum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.positive_rank_point_spectrum"),
                H("positive rank point spectrum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When rank(D)>0, the actual algebraic point spectrum is exactly cast(h+N). A frequency-one oscillator on a minimizing charge realizes every n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-zero-rank-point-spectrum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.zero_rank_point_spectrum"),
                H("zero rank point spectrum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When rank(D)=0, original omega vanishes and the actual carrier is the existing nonzero vacuum line. The actual point spectrum consists exactly of zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-bottom-fiber"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.bottom_fiber"),
                H("bottom fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A label has bottom weight if and only if its charge minimizes q_mu and its oscillator exponent is zero. Several minimizing charges are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-conformal-mode-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.conformal_mode_grade"),
                H("conformal mode grade"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual Virasoro mode L_m maps the actual rational energy-e grade to the energy-(e-m) grade for all integer m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-positive-modes-kill-bottom"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.positive_modes_kill_bottom"),
                H("positive modes kill bottom"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every positive actual conformal mode kills EVERY vector in the full bottom space. This does not assert Virasoro generation from that space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-zero-rank-minimum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.zero_rank_minimum"),
                H("zero rank minimum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed rational minimum h equals zero in rank zero, by the existing collapse of all actual labels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-halfshiftlattice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.halfShiftLattice"),
                H("halfShiftLattice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rank-one even integral lattice has Gram matrix [2]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetspectrum-half-shift-two-minima"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetSpectrum.half_shift_two_minima"),
                H("half shift two minima"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Gram [2], mu=1/2 satisfies exact duality with beta=1. The GLOBAL bottom is 1/4 and two distinct integral charges, zero and minus one, attain it."))),
                DescribeRole.Theorem))));
}
