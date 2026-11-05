using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class CyclicGroundOrbitFixedSpaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-return holonomy classifies fixed vectors supported on one actual lattice charge cycle.",
        H("First-Return Ground Fixed Space"),
        Blocks(
            Paragraph(Text(
                "Fix an integral symmetric even lattice datum D, an additive charge automorphism g preserving its bilinear form, an additive sign character chi, and an actual norm-four charge a. Only this charge is required to have a positive return period m; the operator and other charges need not have finite order. Let d be the minimal positive charge period, T the existing corrected lattice lift, e the literal ground vector with charge a, and u the sum of T^j e for zero through d minus one. The subspace S is the literal complex span in Carrier D of the zero-oscillator ground vectors on this charge cycle.")),
            Describe.Lean(
                DescribeId.Create("cyclicgroundorbitfixedspace-firstreturn-ground-fixedspace"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitFixedSpace.first_return_ground_fixed_space"),
                H("Actual charge-cycle classification and normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every such D, g, bilinear-preservation proof, chi, a, m, positive-period proof and charge-return proof, the intersection of S with the corrected fixed submodule is the span of u when T^d e equals e, and is zero otherwise. In both branches the actual carrier coefficient of u at charge a and zero oscillator exponent is one, so u is nonzero. The period m is only a witness of periodicity; the criterion always uses d."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The corrected-power formula of CyclicIsometryLift gives the actual phase and charge of every transformed ground vector. The injectivity of charge iterates and Mathlib's minimal-period distinctness isolate each coordinate. Fixedness then transports the starting coefficient around the entire cycle and reconstructs every supported fixed vector as that coefficient times u. The starting coefficient of u is one because only the identity iterate contributes there. Telescoping T u minus u leaves exactly T^d e minus e, which forces the coefficient to vanish when the first-return phase is nontrivial.")),
            Paragraph(Text(
                "A nonzero first-cycle sum can therefore coexist with a zero fixed space: in the obstructed branch u is nonzero but is not fixed. A longer full-period average can cancel even though the first-cycle sum does not. Trivial total phase permits a fixed line even when individual steps have nontrivial phases. This local statement supplies the missing phase-sensitive bridge from charge dynamics to the actual lattice ground sector; the monomial-cycle principle is classical linear algebra and carries no novelty claim.")),
            Paragraph(Text(
                "The result assumes neither rootlessness nor positivity nor finiteness of the whole norm-four shell. It does not yet construct a basis or dimension formula for the full ground span, count neutral oscillator or whole grade-two states, identify the full C2 quotient, or provide a coherent lift of the full isometry group. The source reuses the existing carrierBasis, corrected_pow_single and geometric_shift; no surrogate representation or fixedness premise replaces the actual lattice operator.")))));
}
