using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class TransverseHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original transverse BPZ/Hermitian positivity on the integral charge and oscillator carrier.",
        H("Original Transverse Hermitian Norm"),
        Blocks(
            Paragraph(Text("The form is canonical OriginalMatterHermitian.Hm x y = sourcePairing D (theta D (kappaCarrier x)) y. The source pairing, reflection, conjugation, original integral charges and oscillator carrier are unchanged. RealOrthonormalFrame is a local real orthonormal positive subspace hypothesis of the original possibly indefinite integral Gram; there is no whole-Gram positivity, rank-26 or nonzero-charge assumption.")),
            Paragraph(Text("The exact norm is the finite sum over charges a and occupation vectors alpha of the product over colour/mode pairs (j,r) of alpha(j,r)! times (r+1)^alpha(j,r), multiplied by normSq of the coefficient of x(a). No half-frequency, occupation factorial, phase conjugation or charge row is omitted. Original Wick contraction and theta signs are proved to cancel before the comparison with the independently defined factorial form.")),
            Paragraph(Text("This is classical symmetric/Bargmann Fock normalization applied to the repository's original source form, with no literature novelty claim. The reused native factorial and current substitution results retain their original provenance and licenses. The finite-support polynomial identity proves positivity on the transverse image only; it supplies no analytic completion, positivity on the whole indefinite carrier, p0 BRST cohomology or full no-ghost theorem. The full Monster/VOA/CFT/anomaly/fusion/BRST/string/AdS programme remains unfinished.")),
            Paragraph(Text("The six public theorem registrations remain OPEN: the source-owner Reg mirror, exact source selection/reconstruction, lawful realization bridge and readout law, whole-family variation and sensitivity, and observational dependence have not been supplied. No declared_validated status is claimed. The linked-issue disclosure is https://github.com/the-omega-institute/trureturing/issues/25831.")),
            Node("E", "Original coordinate space", "The finite coordinate space is Fin D.rank to complex numbers.", DescribeRole.Definition),
            Node("originalG", "Original bilinear Gram form", "Uses the original integral Gram matrix with no global positivity hypothesis.", DescribeRole.Definition),
            Node("RealOrthonormalFrame", "Real orthonormal transverse frame", "A frame has real complex coordinates and its bilinear Gram matrix is the identity; t and the original lattice rank may be zero.", DescribeRole.Definition),
            Node("Polynomial", "Transverse polynomials", "Polynomials have variables indexed by transverse colour and every natural mode.", DescribeRole.Definition),
            Node("Occupation", "Finite occupation indices", "An occupation is a finitely supported natural exponent vector on all transverse modes.", DescribeRole.Definition),
            Node("lin", "Original linear oscillator", "Maps a transverse generator into the genuine linear combination of original oscillator variables at the same mode.", DescribeRole.Definition),
            Node("phi", "Original polynomial embedding", "Extends the frame linear combinations by the native free polynomial algebra homomorphism.", DescribeRole.Definition),
            Node("annihilateAlong", "Original directional annihilation", "A derivation formed from the existing original Gram-weighted annihilation derivations.", DescribeRole.Definition),
            Node("annihilateAlong_phi", "Transverse chain rule", "On every polynomial, original directional annihilation of the frame substitution equals substitution of the transverse partial derivative. The generator calculation uses frame Gram orthonormality, and Leibniz extends it.", DescribeRole.Theorem),
            Node("bpzOsc", "Literal reflected conjugate Wick form", "Applies the existing integerWick to sigma of canonical kappaOsc of phi in the first slot, and phi in the second. This definition does not mention a positive target form.", DescribeRole.Definition),
            Node("frequencyScale", "Integer frequency square root", "The scale is the real square root of r+1, cast to complex numbers, for every natural r.", DescribeRole.Definition),
            Node("rescale", "Invertible frequency substitution", "Reuses OriginalCurrentMetric.substitutionEquiv with the derived diagonal frequency matrix and its two-sided inverse. It scales each mode-r generator by sqrt(r+1).", DescribeRole.Definition),
            Node("bpzOsc_eq_target", "Original Wick to factorial comparison", "The literal reflected conjugate original Wick form equals FactorialFockMetric.inner after frequency rescaling, for every pair of transverse polynomials. Real frame coordinates give conjugation compatibility; theta contributes the sign which cancels the signed Wick contraction, leaving frequency r+1. The comparison follows from the original creation recurrence and the factorial creation/partial-derivative law.", DescribeRole.Theorem),
            Node("delta", "Single original charge embedding", "Retains any original integral charge and substitutes its transverse polynomial into the original oscillator.", DescribeRole.Definition),
            Node("source_delta_delta_eq_factorial", "Exact charge delta and factorial form", "For any original integral charges a and b, including zero, canonical Hm of the embedded states equals the rescaled factorial inner product when a=b and zero otherwise. The charge equality follows from the original opposite-charge sourcePairing and literal theta reflection.", DescribeRole.Theorem),
            Node("transverseEmbed", "Finite original charge embedding", "Maps each component of the original finite charge support by phi, with no charge quotient, cutoff or suppressed frequency.", DescribeRole.Definition),
            Node("frequencyWeight", "Occupation frequency product", "The weight is the product of (r+1) to the occupation of each colour/mode variable, including the empty product.", DescribeRole.Definition),
            Node("exactWeight", "Exact factorial and frequency weight", "Multiplies FactorialFockMetric.weight, the product of occupation factorials, by frequencyWeight. Every such natural weight is strictly positive.", DescribeRole.Definition),
            Node("rescaled_inner_coeff_sum", "Exact rescaled coefficient norm", "For every transverse polynomial P, the factorial self-pairing after rescale is the finite sum of exactWeight times normSq of each original coefficient. The proof computes the actual rescaled monomials and their coefficients; sqrt(r+1) squared supplies exactly the frequency product.", DescribeRole.Theorem),
            Node("Hm_self_eq_exact_finite_sum", "Original finite-charge coefficient norm", "For every finitely supported original charge family x, canonical Hm of its transverse embedding with itself equals the sum over x.support and each polynomial support of exactWeight times coefficient normSq. All original charge rows, including zero, are retained.", DescribeRole.Theorem),
            Node("Hm_self_strict_positive", "Strict positivity on the original transverse image", "For every nonzero finite-charge transverse polynomial family, the literal original embedded Hm self-pairing has imaginary part zero and strictly positive real part. A nonzero charge component and a nonzero polynomial coefficient supply a strictly positive term in the exact finite sum.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("transverse-hermitian-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
