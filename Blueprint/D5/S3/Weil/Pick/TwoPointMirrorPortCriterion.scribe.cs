using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class TwoPointMirrorPortCriterionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Pick/TwoPointMirrorPortCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two regular upper-half-plane locations detect the cross residue of a finite mirror-resolvent pair.",
        H("Two-point mirror port criterion"),
        Blocks(
            Paragraph(Text(
                "Let mu be nonreal and let C be an arbitrary complex square matrix on a finite port space. " +
                "The transfer is C divided by mu minus z, plus the adjoint of C divided by the conjugate of mu minus z. " +
                "Its Nevanlinna blocks are the difference of the transfer at z and its adjoint at w, divided by z minus the conjugate of w. " +
                "Choose two distinct locations in the open upper half-plane, neither equal to either nominal pole. " +
                "The full two-location Gram retains all ports at each location; no invertibility or rank condition is imposed on C.")),
            Describe.Lean(
                DescribeId.Create("two-point-mirror-invertible-congruence"),
                DeclarationHandle.Create(Module + "two_point_mirror_congruence"),
                H("An invertible Cauchy congruence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Gram equals the lifted two-point Cauchy feature matrix times the zero-scale spectral localizer of C times the adjoint feature matrix. " +
                    "The localizer has zero diagonal blocks and off-diagonal blocks C and its adjoint. " +
                    "An explicit inverse certifies invertibility of the feature matrix: its scalar determinant is nonzero because both poles and both locations are distinct and all four pole denominators are nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-mirror-positive-iff-zero-residue"),
                DeclarationHandle.Create(Module + "two_point_mirror_posSemidef_iff"),
                H("Two-point positivity detects exactly the cross residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same pole, distinctness, upper-half-plane and regularity assumptions, the full Gram is positive semidefinite if and only if C is zero. " +
                    "Invertible congruence transfers positivity to the localizer. Its trace is zero, so positive semidefiniteness forces the entire localizer, and hence C, to vanish. " +
                    "For bilateral ports the residue is the adjoint of the minus port times the plus port; separate nonvanishing of the two maps does not ensure a nonzero cross residue."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-point-even-port-positive-iff-zero-probe"),
                DeclarationHandle.Create(Module + "two_point_even_port_posSemidef_iff"),
                H("Every nonzero even probe is visible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the two port maps are equal to G, the residue is the Hilbert Gram formed by the adjoint of G times G. " +
                    "For the same admissible two locations, positive semidefiniteness is equivalent to G being zero. " +
                    "This criterion includes singular probes and empty finite spaces. It detects visibility of one conjugate pole pair; it does not count all negative squares or identify the finite transfer with a completed-zeta or Weil realization."))),
                DescribeRole.Theorem))));
}
