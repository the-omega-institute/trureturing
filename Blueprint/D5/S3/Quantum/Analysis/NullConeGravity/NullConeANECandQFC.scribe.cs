using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullConeANECandQFCDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC.";
    private static readonly LibraryNoteRef NullLocal =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");
    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global Raychaudhuri evolution constrains the total Ricci integral. The generalized entropy derivative gives stationary-cut quantum focusing, an entropy monotonicity theorem, and an integrated energy inequality.",
        H("Global focusing and generalized entropy"),
        Blocks(
            Paragraph(Text("The focusing identity allows continuous integrable Ricci curvature of either sign. The quantum results use a scalar entropy and positive area along an affine generator, with the Raychaudhuri equation and quantum focusing or energy inequalities stated as mathematical hypotheses. The references concern null-local modular flow and the corresponding null-cone gravitational setting.")),
            Entry("raychaudhuri-global-tendsto-zero", "raychaudhuri_global_tendsto_zero", "Two-ended decay of global expansion",
                "For a global Raychaudhuri solution with continuous integrable Ricci term of arbitrary sign, its Ricci primitive is bounded by the integral of its absolute value. Adding the primitive to the expansion gives a decreasing function. The existing finite-affine focusing bound applied to a shifted expansion and to its time reversal bounds this function on both sides. The nonnegative optical loss is consequently integrable, as are the squared expansion and the expansion derivative. Both endpoint limits exist and must vanish because the squared expansion is integrable."),
            Entry("raychaudhuri-global-anec-identity", "raychaudhuri_global_anec_identity", "Global integrated focusing identity",
                "The focusing density θ²/2 + σ² is nonnegative. Integrating its derivative relation with the compensated expansion on increasing compact intervals and taking both infinite endpoints proves integrability and identifies its total integral with minus the Ricci integral."),
            Entry("anec-global-rigidity", "anec_global_rigidity", "Global rigidity under averaged null energy",
                "Nonnegative total Ricci curvature forces zero total focusing density. Nonnegative squares and continuity of the expansion imply pointwise vanishing of the expansion. The derivative equation then gives an almost-everywhere zero Ricci term, which vanishes everywhere by its continuity. The same equation gives pointwise zero shear, and the Ricci integral is zero."),
            Entry("strict-anec-forces-caustic", "strict_anec_forces_caustic", "Obstruction to global regular expansion",
                "Strictly positive total Ricci curvature contradicts the nonnegative integral of the focusing density. Hence a regular expansion solving the equation cannot be defined on the entire affine line."),
            Entry("nec-and-global-forces-zero-ricci", "nec_and_global_forces_zero_ricci", "Pointwise null energy rigidity",
                "Nonnegative Ricci curvature implies the averaged hypothesis. The expansion and shear vanish, and the Raychaudhuri equation yields zero Ricci curvature pointwise."),
            Entry("generalized-entropy", "generalizedEntropy", "Generalized entropy",
                "At each affine parameter, divide the area by 4Gℏ and add the exterior matter entropy.", DescribeRole.Definition),
            Entry("quantum-expansion", "quantumExpansion", "Quantum expansion",
                "Multiply the affine derivative of generalized entropy by 4Gℏ divided by the area.", DescribeRole.Definition),
            Entry("quantum-expansion-eq", "quantum_expansion_eq", "Generalized entropy and quantum expansion",
                "The area derivative equals expansion times area. Differentiating generalized entropy and multiplying by four times Newton's constant times Planck's constant divided by area yields the classical expansion plus the rescaled entropy derivative."),
            Entry("quantum-expansion-deriv", "quantum_expansion_deriv", "Derivative of quantum expansion",
                "The reciprocal-area derivative contributes the correction proportional to minus the expansion times the entropy derivative. Combining this with the Raychaudhuri equation gives the full quantum expansion derivative."),
            Entry("qfc-iff-qnec-at-stationary-cut", "qfc_iff_qnec_at_stationary_cut", "Stationary-cut equivalence",
                "At a cut with vanishing expansion and shear the quantum focusing inequality reduces to the quantum null energy inequality. Dividing by the positive factor 8πG cancels Newton's constant exactly, leaving the entropy second derivative times ℏ/(2πA)."),
            Entry("qfc-implies-gsl", "qfc_implies_gsl", "Generalized second law on a future horizon",
                "Under quantum focusing the quantum expansion is antitone. If there are arbitrarily late cuts where it is at least minus any positive tolerance, every earlier value is nonnegative. Positivity of the area and constants transfers this sign to the generalized entropy derivative, proving entropy monotonicity on the future ray."),
            Entry("qnec-implies-anec", "qnec_implies_anec", "Integrated quantum null energy inequality",
                "With positive constant area and Planck's constant, integrate the pointwise QNEC inequality on finite intervals. The fundamental theorem of calculus rewrites the entropy second derivative integral as the difference of entropy first derivatives. Both endpoint derivatives tend to zero, and the integrable stress tensor has a finite total integral, which is nonnegative."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullLocal, NullCone),
            Blocks(Paragraph(Text(statement))), role);
}
