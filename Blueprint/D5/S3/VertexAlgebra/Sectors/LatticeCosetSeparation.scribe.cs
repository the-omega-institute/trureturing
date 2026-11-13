using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetSeparationDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("coset-separation-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetSeparation." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetSeparation", H("Uniform transverse target transport"), Blocks(
            D("transversePolynomial", "The complex algebra homomorphism that substitutes the actual ambient transverse oscillator T(j,k)=X(new j,k)-sum_i (HB)(i,j) X(old i,k) into an arbitrary polynomial in external indices and natural oscillator frequencies.", DescribeRole.Definition),
            D("mixedState", "For every external target sector d and every transverse polynomial h, the complex linear map sending single(n,f) to the actual ambient state single((n,d),injection(f) times h(T)). All original finite-charge states and arbitrary target polynomials are included.", DescribeRole.Definition),
            D("current_mixed_polynomial", "For positive definite original D, every old direction i, external sector d, original charge n, integer mode m, arbitrary original oscillator polynomial f and arbitrary transverse polynomial h, the native ambient old current on injection(f) h(T) equals injection of shiftedCurrentPolynomial(D,Bd,1,i,n,m,f) times h(T). Positive modes annihilate every transverse factor because G HB=B. Negative and zero modes retain their native multiplication and integral charge pairing. Neither ambient positivity nor nondegeneracy is assumed.", DescribeRole.Theorem),
            D("current_mixed", "For the same arbitrary ranks and original positivity, every old direction i, sector d, integer mode m, original finite-charge state g and arbitrary transverse polynomial h, the full ambient neutralMode on mixedState(d,h,g) equals mixedState(d,h) applied to the corresponding mode of the already truncated native shifted-current action with integral dual pairing Bd. This uses action_current_coefficients and imposes no polynomial weight or degree cutoff.", DescribeRole.Theorem),
            D("transverseTranslation", "For every external source charge a, evaluate an arbitrary transverse polynomial at C(T(j,k)) minus C(transversePair(a,j)) times the translation variable to power k+1. This retains the transverse variables before projection.", DescribeRole.Definition),
            D("translated_mixed_polynomial", "For every positive definite original D, external source a, original source charge n, old polynomial f and arbitrary transverse target h, the full native translatedPolynomial at (n,a) of injection(f) h(T) factors as the native translation of injection(f) times transverseTranslation(a,h). The cancellation of n in the transverse shift is proved before projection. No field-factorization hypothesis is assumed.", DescribeRole.Theorem),
            D("multiply", "For any native LatticeData F and actual oscillator polynomial t, multiply every charge-sector polynomial by t, as a complex linear endomorphism of the original Carrier F.", DescribeRole.Definition),
            D("ground_transverse_commutator", "For every positive definite original D, arbitrary external source charge a, original charge n, transverse index j and frequency k, integer mode m and every ambient target state v, the actual charged field at (n,a) applied to T(j,k)v equals T(j,k) times its mode m on v minus transversePair(a,j) times its mode m-(k+1) on v. The finite native polynomial convolution proves the relation, retaining the full original integral zero-mode exponent and epsilon with its half diagonal.", DescribeRole.Theorem),
            Paragraph(Text("The oscillator conventions are those of Bakalov-Kac, math/0402315v1, section 4.1. These results prove uniform target transport and its charged generator relation. The complete two-source projected composition still requires the all-state creation-factor expansion and finite inner-first coefficient assembly; no complete intermediate-projection formula or analytic CFT realization follows from this module alone.")))));
}
