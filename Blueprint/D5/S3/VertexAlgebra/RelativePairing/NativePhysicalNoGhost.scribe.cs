using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.RelativePairing;

internal sealed class NativePhysicalNoGhostDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/RelativePairing/NativePhysicalNoGhost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ambient Lorentzian signature makes the negative original right-C0 form strictly positive on every nonzero literal fixed-sector physical image class.",
        H("Conditional Literal Physical No-Ghost"),
        Blocks(
            Paragraph(Text("The carrier is exactly OriginalQPhysicalPairing.physicalImage, the image of the actual relative ghost-one charge-energy sector in OriginalCohomology. Its quotient still uses unrestricted OriginalBoundaries. Both Gram inverse equations and both frame inverse equations, rank 26, the null direction, nonzero chosenP, distinct longitudinal axes, literal null and adapted-partner rows, both dual-row equations and chosenH plus level minus one equal to zero are retained. Every frame row is explicitly star-fixed. The signature premise concerns ActualSignature.signature of the actual real ambient Gram quadratic form and equals rank minus two. No transverse positive-definiteness, physical/native isometry, nonzero projection, occupation cutoff or positivity of a quotient is supplied as a hypothesis.")),
            Describe.Lean(DescribeId.Create("literal-two-slot-oscillator-recovery"),
                DeclarationHandle.Create(Prefix + "imageForm_projection"),
                H("Arbitrary Original Quotient Pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary first and second classes in the literal physicalImage, nativeImage_imageProjection recovers each class. The actual nativeImage_form then identifies imageForm on the pair with minus fockForm on the two transverseDownOscillator values extracted by imageProjection. This is a consumed bind-only helper, not an independent novelty claim. The right-C0 convention and its negative sign are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-conditional-no-ghost-and-radicals"),
                DeclarationHandle.Create(Prefix + "imageForm_noGhost"),
                H("Positive Real Diagonal And Zero Radicals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof does not assume that extracted coefficients or their actual oscillator are nonzero. nativePhysicalEquiv and the actual imageProjection/nativeImage inverse law imply nonzero coefficients from a nonzero original class. The actual coordinates_downState finite reconstruction and downState_tensor then force the actual transverseDownOscillator to be nonzero. A finite linear combination of transverse monomials reconstructs this oscillator through nativePolynomial; support excludes the two longitudinal axes, and mapDomain/comapDomain recovers every original finite exponent family. Hence its native transverse polynomial is also nonzero.")),
                    Paragraph(Text("LorentzianSignature.transverseGram_posDef consumes the actual ambient signature and star-fixed frame. Its hyperbolic-plane/transverse signature splitting derives, rather than assumes, transverse positive-definiteness. The existing nativePolynomial_positive and nativePolynomial_norm_real provide strict positivity of the real diagonal and vanishing imaginary part. The arbitrary two-slot original quotient comparison gives 0 less than the real part of minus imageForm(z,z), and imaginary part zero, for every nonzero literal z. Testing either original-form radical against z itself proves its only member is zero.")),
                    Paragraph(Text("This is a conditional same-sector algebraic no-ghost consequence, not a construction of the supplied real adapted frame. Nonzero chosenP excludes the neutral exception. It proves neither all-charge no-ghost nor a theorem on all original cohomology. The complete moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT objective remains open. Source admission, four-slot audit completion, remote publication and full consumer checks are separate from a kernel proof; none is asserted by this exposition."))),
                DescribeRole.Theorem))));
}
