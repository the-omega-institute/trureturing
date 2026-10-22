using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charged projected-ground residue rows on the original actual half-Fock tensor carrier.",
        H("Charged Two-Order Physical Residue"),
        Blocks(
            Paragraph(Text("For D:LatticeData, hu:IsUnit D.G.det, signed charges sigma and tau, Boolean projected signs, "
                + "signed lifts gamma, delta, r, n, and arbitrary x:ActualTensor D hu, the source and collision rows "
                + "retain all four reflected charge components. The output exponent is the unreduced integer "
                + "-2*(n-l)-gamma-delta-2, and the physical residue keeps both ordered branches with the public "
                + "integerBinomial convention.")),
            Describe.Lean(
                DescribeId.Create("charged-residue-ground-source-collision"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue.charged_ground_source_collision"),
                H("The public all-N source comparison is composed on all four projected components"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The projected-ground expansion is performed on Carrier D. Each reflected bare source "
                    + "is transported by the public all-N comparison to the normalized collision coefficient on "
                    + "ActualTensor D hu. Ground-action multiplication supplies the single actual cocycle and the "
                    + "chargeScalar normalization; no private all-N endpoint or second cocycle is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-source-row-collision-row"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_eq_collision"),
                H("Concrete physical source rows equal the four reflected collision rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Every signed row index and every actual tensor input is retained. The theorem is the "
                    + "source side of the intended residue comparison and does not identify the physical two-order "
                    + "residue with that row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-projected-slice-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue.projectedGround_slice_mode_expansion"),
                H("Projected physical slices expand into both reflected charged fields"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The expansion is pointwise on the original ActualTensor carrier and preserves the "
                    + "signed lift and exact physical exponent. Both reflected components remain available to the later "
                    + "ordered-kernel telescope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-collision-tail"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue.chargedPhysicalCollisionRow_tail"),
                H("The four reflected collision rows have an independent unweighted outer tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For l at or beyond ((K:Int)-r).toNat, with natAbs(bilinear sigma tau) ≤ K, "
                    + "every reflected source degree is negative. This includes zero charge, rank-zero data, K=0 and "
                    + "the boundary l=L."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-ordered-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_left_finite"),
                H("The left physical branch has pointwise finite support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The corresponding right branch is recorded by chargedPhysicalResidueRow_right_finite. "
                    + "The finite support bounds come from the actual input order of the inner field, separately for "
                    + "each branch; neither branch is declared zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-finite-inverse"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedResidue.charged_finite_binomial_inverse"),
                H("Finite binomial inversion is proved with the zero-cutoff case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The finite triangular inverse reindexes finite sums and consumes Ring.add_choose_eq. "
                    + "L=0 is discharged from the explicit tail rather than a positive-cutoff argument. Its charged "
                    + "forward-row and complete-physical-residue hypotheses still have to be instantiated; neither is "
                    + "smuggled into this theorem as an assumption."))),
                DescribeRole.Theorem),
            Paragraph(Text("The construction uses the public StateFieldResidueReconstruction integerBinomial, physicalSlice_mode, "
                + "native_ordered_product and the existing actual ground-action/collision APIs. The remaining mathematical "
                + "gap is the native two-order forward telescope on arbitrary actual inputs, followed by an independent "
                + "complete-residue tail and charged-family inverse instantiation. No full VOA, CFT, string or AdS/CFT "
                + "claim is made. Classical residue and twisted-lattice background is attributed to the inherited "
                + "repository sources and FLM; no literature novelty is asserted."))));
}
