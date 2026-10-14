using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostAuxiliarySelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rotated tensor auxiliary support",
        H("Actual rotated tensor auxiliary support"),
        Blocks(
            Paragraph(Text("The pairing is literally LatticeBcGhostHermitianForm.F on the unrestricted original State. Its existing F_tmul multiplies the charge-diagonal Hermitian oscillator form by BcGhostRotatedForm.Hplus. The real-row arbitrary-polynomial Fock selection is reused, not reproved. The total native auxiliary degree is matterAux + ghostNumber - 1. Ghost degree sums three before insertion and two after the actual right C0 insertion combine with matter degree sum zero to give total thresholds one and zero. Finite charge, polynomial and ghost expansions retain arbitrary complex coefficients, with conjugation in the left slot. Span induction needs no frame inverses, Gram inverses, critical rank, orthonormality or positivity. This structural selection is not an original physical no-ghost theorem or a completed string/AdS bridge.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-factor-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_factor_selection"),
                H("Actual polynomial factor selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual charge-diagonal matter form and the actual rotated Hplus select total auxiliary sum one. Longitudinal rows are real, distinct and exactly dual; transverse rows may be complex. No inverse Gram, frame inverse, rank, energy, positivity or occupation hypothesis is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-factor-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_factor_selection"),
                H("Actual inserted polynomial factor selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal right C D 0 insertion raises ghost number by one. The surviving total auxiliary sum is zero, with a = matterAux + ghostNumber - 1 in each slot. The right ghost is rotated, not replaced by the unrotated BPZ or Hghost form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-nativeword-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_nativeWord_selection"),
                H("Native word selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite native down-word is converted using the existing polarized J eigenvalue and the original homogeneous support equivalence. Arbitrary monomial exponents and arbitrary charges retain the exact uninserted threshold one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-nativeword-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_nativeWord_selection"),
                H("Inserted native word selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual original tensor carrier and right C0 insertion select nativeDegree sums zero. The normalization of the down vacuum is not used as an assumed factorization law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-nativecoefficients-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_nativeCoefficients_selection"),
                H("Finite native coefficient expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original native_sector_finite_expansion reconstructs arbitrary charge-sector states. Both frame inverse equations are needed only for these coordinates. The proof sums actual monomial pairs with conjugated left coefficients and linear right coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-nativecoefficients-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_nativeCoefficients_selection"),
                H("Inserted finite native coefficient expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual C0 linear map passes through the genuine finite expansion. Every pair of occupied native coefficients with nonzero total auxiliary sum has zero inserted readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-signedenergyfiltration-vanishing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_signedEnergyFiltration_vanishing"),
                H("Absolute signed-span vanishing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary states in the two actual signedEnergyFiltration spans, lowerL + lowerR > 1 forces the uninserted F pairing to vanish. Charges and levels may differ. This does not assert vanishing for lower-one against lower-zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-signedenergyfiltration-vanishing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_signedEnergyFiltration_vanishing"),
                H("Inserted signed-span vanishing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two independent submodule span inductions extend the native word law to actual unrestricted finite states. The precise inserted condition is lowerL + lowerR > 0; no coordinate inverse or energy bound is added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-two-slot-cancellation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_two_slot_cancellation"),
                H("Actual two-slot inserted cancellation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both base vectors lie in their actual lower-zero spans and both tails lie in lower-one spans. Each of the three inserted correction terms vanishes, including the tail-tail term. This is not a claim about the unreleased finite HPL tail, energyReducedInclusion, isometry, positivity, radicals or physical quotient descent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-down-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_down_normalization"),
                H("Actual inserted down normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original down is j and its actual c(0) image is k. Hplus j k is minus one because the actual energy half-turn rotates k to basis {1,3}. The arbitrary native matter inserted readout is minus hermitianForm, not plus hermitianForm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-native-empty-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_native_empty_normalization"),
                H("Native empty-ghost word normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary original charges and arbitrary matter monomials, the empty polarized ghost-word C0 pairing is the negative charge-diagonal oscillator Fock form. No norm or positivity interpretation is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostauxiliaryselection-f-c0-native-two-slot-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeBcGhostAuxiliarySelection.F_c0_native_two_slot_normalization"),
                H("Actual native two-slot normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Native empty-ghost matter words of nonnegative auxiliary weight lie in the actual lower-zero spans at their own native levels. Arbitrary actual lower-one tails in both slots leave the inserted readout equal to the negative charge-diagonal oscillator form. This consumes the actual sign computation and the two-slot support cancellation without identifying these tails with the unreleased finite HPL correction."))),
                DescribeRole.Theorem))));
}
