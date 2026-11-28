using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class TwoPointMirrorPortCriterionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Pick/TwoPointMirrorPortCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two sample-port coordinates detect every nonzero cross residue of a finite mirror-resolvent pair.",
        H("Two-point mirror port criterion"),
        Blocks(
            Paragraph(Text(
                "Let mu be nonreal and let C be an arbitrary complex square matrix on a finite port space. " +
                "The transfer is C divided by mu minus z, plus the adjoint of C divided by the conjugate of mu minus z. " +
                "Its Nevanlinna blocks are the difference of the transfer at z and its adjoint at w, divided by z minus the conjugate of w. " +
                "Choose two distinct complex locations, neither equal to either nominal pole, with every location different from the conjugate of each location. Any two distinct regular locations in the open upper half-plane satisfy these conditions. " +
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
                    "Under the same pole, distinctness, cross-denominator and regularity assumptions, the full Gram is positive semidefinite if and only if C is zero. " +
                    "Invertible congruence transfers positivity to the localizer. Its trace is zero, so positive semidefiniteness forces the entire localizer, and hence C, to vanish. " +
                    "For bilateral ports the residue is the adjoint of the minus port times the plus port; separate nonvanishing of the two maps does not ensure a nonzero cross residue. " +
                    "When the two port maps are equal to G, the residue is the Hilbert Gram formed by the adjoint of G times G. " +
                    "For the same admissible two locations, positive semidefiniteness is equivalent to G being zero. " +
                    "This criterion includes singular probes and empty finite spaces. It detects visibility of one conjugate pole pair; it does not count all negative squares or identify the finite transfer with a completed-zeta or Weil realization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-coordinate-mirror-negative-principal-minor"),
                DeclarationHandle.Create(Module + "two_point_mirror_negative_principal_minor"),
                H("Two coordinates suffice to detect a nonzero residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every admissible pair of locations, C is nonzero if and only if there are distinct sample-port coordinates p and q such that the real part of G(p,p)G(q,q) minus G(p,q)G(q,p) is strictly negative. " +
                    "Thus a two-by-two principal submatrix already detects indefiniteness, regardless of the number of ports. " +
                    "If a diagonal entry C(i,i) is nonzero, use port i at both locations: the determinant is minus the squared modulus of C(i,i) times the squared modulus of the scalar Cauchy determinant. " +
                    "If all diagonal entries of C vanish, all diagonal entries of G vanish. The nonzero residue forces G to be nonzero; any nonzero off-diagonal entry then gives a principal determinant equal to minus its squared modulus. " +
                    "Conversely, a zero residue gives the zero Gram and excludes a negative minor. The selected coordinates may use one location or both. This conclusion concerns the finite mirror-resolvent model and supplies no identification with a zeta transfer function."))),
                DescribeRole.Theorem))));
}
