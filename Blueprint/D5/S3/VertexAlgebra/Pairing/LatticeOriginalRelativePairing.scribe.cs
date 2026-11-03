using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Pairing;

internal sealed class LatticeOriginalRelativePairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original all-charge relative tensor pairing with arbitrary complex transverse basis and signed-degree selection.",
        H("Original relative tensor pairing"),
        Blocks(
            Paragraph(Text("The construction uses the canonical OriginalMatterHermitian Hm, the original signed ghost form, and literal c0 insertion on the all-integral-charge Carrier tensor occupation Fock. Reality is assumed only for the two longitudinal null vectors; the transverse basis is an arbitrary complex basis of their actual orthogonal complement.")),
            Paragraph(Text("The public theorem escape audit remains unfinished. Issue https://github.com/the-omega-institute/trureturing/issues/25857 records the missing realization, exact reconstruction, lawful template, whole-family variation, sensitivity, and observational-dependence evidence. This issue is the documented audit exception and is not a validated registration. The full BRST/HPL/no-ghost and string programme remains outside this unit.")),
            Node("matter-form", "Canonical matter sesquilinear form", "The matter form is the canonical frame-free Hm."),
            Node("hm-single", "Charge-diagonal matter pairing", "Single-charge states pair through integerWick with the original signed oscillator conjugation."),
            Node("hm-ground", "Ground-state charge pairing", "Every integral momentum, including zero, has the same unit ground norm on the matching charge."),
            Node("conjugate-k", "Conjugation on the transverse complement", "The conjugated transverse vector remains in the actual orthogonal complement under the two longitudinal reality hypotheses."),
            Node("conjugate-k-expansion", "Arbitrary complex-basis conjugation transport", "Conjugation is expanded in the supplied complex transverse basis without imposing reality or orthonormality on that basis."),
            Node("direction", "Complete-basis directions", "The complete basis consists of the two longitudinal directions and the supplied transverse basis."),
            Node("phi", "Inverse coordinate equivalence", "The polynomial coordinates are transported to the original oscillator algebra by the inverse coordinate equivalence."),
            Node("kappa-phi-transverse", "Transverse conjugation transport", "The conjugate of a transverse generator is the finite complex basis combination obtained from conjugateK."),
            Node("kappa-phi-x", "Generator conjugation transport", "The original oscillator conjugation is transported on every complete-basis generator."),
            Node("original-derivative", "Original annihilation derivation", "The derivative is the original Gram-weighted annihilation derivation."),
            Node("coordinate-derivative", "Complete-basis coordinate derivation", "The coordinate derivation uses the actual Gram pairings against the complete basis."),
            Node("derivative-transport", "Derivative transport", "The original derivative and the complete-basis coordinate derivative are intertwined by the inverse coordinate equivalence."),
            Node("integer-wick-lin-creation", "Creation-contraction recursion", "A creation polynomial contracts against integerWick through the original derivative with the signed frequency factor."),
            Node("oscillator-form", "Original oscillator form", "The oscillator form retains the original conjugation and signed Wick form."),
            Node("oscillator-creation", "Oscillator creation recursion", "Creation in the first argument is transferred to the original coordinate contraction in the second argument."),
            Node("oscillator-x-x", "One-particle Gram contraction", "Same-frequency generators pair by the original Gram form, with the signed frequency weight."),
            Node("gram-weight-selection", "Signed Gram selection", "Opposite longitudinal signed weights are required for a nonzero complete-basis Gram coefficient."),
            Node("contraction-support", "Contraction support degree", "Every nonzero contraction coefficient has the degree forced by the derivative variable weight."),
            Node("oscillator-monomial-selection", "Oscillator signed-degree selection", "The Wick induction proves vanishing for every monomial pair whose signed degrees do not sum to zero."),
            Node("matter-basis-selection", "Matter basis selection", "The canonical matter form vanishes on charge-matched basis monomials with non-opposite oscillator degrees."),
            Node("ghost-form", "Signed ghost form", "The ghost form is the canonical signed Hermitian form on the occupation Fock."),
            Node("ghost-relative-signed", "Signed ghost c0 coefficient", "The literal c0 insertion retains both the row sign and Jordan-Wigner phase."),
            Node("ghost-relative-nonzero", "Ghost charge selection", "A nonzero signed ghost coefficient with c0 forces total ghost charge two."),
            Node("total-form", "Original tensor form", "The tensor universal property combines the canonical matter and signed ghost forms."),
            Node("total-form-tmul", "Tensor generator formula", "On pure tensors the total form is the product of the canonical matter and ghost pairings."),
            Node("relative-form", "Relative c0 form", "The relative form inserts c0 on the original ghost tensor factor."),
            Node("relative-form-tmul", "Relative tensor formula", "On pure tensors the relative form is Hm times the signed ghost c0 coefficient."),
            Node("relative-form-actual-basis", "Actual basis formula", "The relative form on the actual basis separates charge, oscillator, and ghost factors."),
            Node("actual-opposite-degree", "Opposite-degree basis orthogonality", "The original basis pairing vanishes whenever the complete state degrees do not sum to zero."),
            Node("actual-support-orthogonal", "Finite support orthogonality", "Finite support separation by signed degree implies orthogonality for arbitrary carrier states."),
            Node("matter-form-apply", "Matter form identity", "The linear-form wrapper evaluates to the canonical Hm."),
            Node("phi-x", "Coordinate generator identity", "The inverse coordinate equivalence sends each polynomial generator to its complete-basis oscillator generator."),
            Node("original-derivative-apply", "Derivative expansion", "The original derivative expands as the finite Gram-weighted annihilation sum."),
            Node("coordinate-derivative-apply", "Coordinate derivative expansion", "The complete-basis coordinate derivative expands as the finite Gram-weighted partial-derivative sum."),
            Node("original-derivative-lin", "Derivative on linear generators", "The original derivative on a linear generator is the same-frequency Gram coefficient."),
            Node("oscillator-one-left", "Vacuum coefficient extraction", "The oscillator form with the unit first argument extracts the constant coefficient."),
            Node("oscillator-right-expansion", "Finite right expansion", "The oscillator form expands over the finite polynomial support of its right argument.")
        )));

    private static DocumentBlock Node(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(name), Handle(name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Prefix + (name switch
    {
        "matter-form" => "matterForm",
        "hm-single" => "Hm_single",
        "hm-ground" => "Hm_ground",
        "conjugate-k" => "conjugateK",
        "conjugate-k-expansion" => "conjugateK_expansion",
        "kappa-phi-transverse" => "kappa_phi_transverse",
        "kappa-phi-x" => "kappa_phi_X",
        "original-derivative" => "originalDerivative",
        "coordinate-derivative" => "coordinateDerivative",
        "derivative-transport" => "derivative_transport",
        "integer-wick-lin-creation" => "integerWick_lin_creation",
        "oscillator-form" => "oscillatorForm",
        "oscillator-creation" => "oscillator_creation",
        "oscillator-x-x" => "oscillator_X_X",
        "gram-weight-selection" => "gram_weight_selection",
        "contraction-support" => "contraction_support",
        "oscillator-monomial-selection" => "oscillator_monomial_selection",
        "matter-basis-selection" => "matter_basis_selection",
        "ghost-form" => "ghostForm",
        "ghost-relative-signed" => "ghost_relative_signed",
        "ghost-relative-nonzero" => "ghost_relative_nonzero",
        "total-form" => "totalForm",
        "total-form-tmul" => "totalForm_tmul",
        "relative-form" => "relativeForm",
        "relative-form-tmul" => "relativeForm_tmul",
        "relative-form-actual-basis" => "relativeForm_actualBasis",
        "actual-opposite-degree" => "actual_opposite_degree",
        "actual-support-orthogonal" => "actual_support_orthogonal",
        "matter-form-apply" => "matterForm_apply",
        "phi-x" => "phi_X",
        "original-derivative-apply" => "originalDerivative_apply",
        "coordinate-derivative-apply" => "coordinateDerivative_apply",
        "original-derivative-lin" => "originalDerivative_lin",
        "oscillator-one-left" => "oscillator_one_left",
        "oscillator-right-expansion" => "oscillator_right_expansion",
        _ => name
    }));
}
