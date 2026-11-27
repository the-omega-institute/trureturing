using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondMassShell4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regulated bulk mass-shell integrals and scaling in four spacetime dimensions.",
        H("The regulated bulk two-point function"),
        Blocks(
            Paragraph(Text("The characteristic covariance problem of Satishchandran and Sorce uses "
                + "the difference of massive and massless scalar two-point functions. The bulk momentum "
                + "integral gives this difference throughout the right half-plane of complex time.")),
            Entry("momentum-energy", "energy", "Momentum energy",
                "For real M and momentum k in three-dimensional Euclidean space, the energy is "
                + "the nonnegative square root of ‖k‖² + M².", DescribeRole.Definition),
            Entry("shell-weight", "shellWeight", "Mass-shell density",
                "The density relative to Lebesgue momentum measure is the reciprocal of "
                + "2(2π)³ times the energy. The massless density takes value zero at zero momentum.",
                DescribeRole.Definition),
            Entry("regulated-integral", "bulkU", "Regulated bulk integral",
                "For real mass M, complex time τ and spatial separation r, integrate the shell density "
                + "against exp(−τ times the energy plus i times the Euclidean inner product of k and r).",
                DescribeRole.Definition),
            Entry("momentum-integrability", "bulkU_integrable", "Momentum integrability",
                "For every real mass and every spatial separation, the momentum integrand is integrable "
                + "when the real part of τ is positive. The energy is at least ‖k‖. Away from k = 0 this "
                + "bounds the integrand by a constant times exp(−Re(τ)‖k‖)/‖k‖. The radial volume factor is ‖k‖²."),
            Entry("holomorphic-time-dependence", "bulkU_differentiableOn", "Holomorphy in time",
                "For fixed real mass and spatial separation, the integral is complex differentiable "
                + "on the right half-plane. Differentiation inserts a factor of minus the energy, "
                + "so a positive local lower bound on the real part of τ gives an integrable exponential bound."),
            Entry("massless-formula", "bulkU_zero", "Massless bulk formula",
                "For every spatial separation r and complex time τ with positive real part, put "
                + "q = ‖r‖² + τ². The massless bulk integral equals the reciprocal of 4π² times q."),
            Entry("massive-difference", "bulkU_difference", "Massive minus massless",
                "For M > 0 and complex time τ with positive real part, the difference of the mass M "
                + "and massless bulk integrals is the bulk correction evaluated at M and q = ‖r‖² + τ². "
                + "At positive real time, Gaussian subordination and the momentum Fourier integral "
                + "give H(M²q/4)/(4π²q). The Schwinger series identifies its difference from the "
                + "massless value with the stated correction. Holomorphic continuation extends the "
                + "formula throughout the right half-plane, where q lies in the slit plane."),
            Entry("radius-scaling", "bulkU_scale", "Joint scaling of time and separation",
                "For nonnegative mass m, positive L and complex time τ with positive real part, "
                + "the mass m integral at (Lτ, Lr) equals L⁻² times the mass mL integral at (τ, r). "
                + "Under k ↦ k/L, three-dimensional volume supplies L⁻³ and the shell density supplies L."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
