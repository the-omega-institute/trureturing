using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class GNSSpectralMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/GNSSpectralMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex continuous spectral moments for the actual prescribed GNS coordinate.",
        H("The spectral family of the original pair"), Blocks(
            Paragraph(Text("The input algebra is any unital complex C-star algebra with its compatible star order. The positive functional psi and its completed GNS representation are genuine Mathlib objects. Its cyclic vector is unnormalized. Zero Hilbert spaces, singular functionals and spectral endpoints remain in scope.")),
            Node("commutant", "The actual represented commutant", "Take the star-subalgebra centralizer of the range of the actual GNS star homomorphism. The triple-centralizer identity makes this a concrete von Neumann algebra. No normality or faithfulness of the representation is needed.", false),
            Node("mem_commutant", "Exact membership", "A bounded operator belongs to this von Neumann algebra exactly when it commutes with every represented algebra element. Closure of the range under star supplies both clauses of the star-subalgebra centralizer.", true),
            Node("spectralHom", "Full complex spectral calculus", "For a positive contraction C, the complex spectrum is real and lies in [0,1]. Real part therefore defines a continuous map from the complex spectrum into the closed posterior interval. Precompose every complex continuous interval function by this map and apply Mathlib's complex cfcHom. The resulting map is a unital complex star algebra homomorphism into the bounded operators, including when the Hilbert space is zero.", false),
            Node("spectralHom_posterior", "The indispensable first moment", "The posterior function x maps exactly to the prescribed C. On its complex spectrum, the complex embedding of real part is the identity, by self-adjoint spectrum restriction. Thus the cfcHom identity theorem applies. The operator is not replaced by an unrelated coordinate.", true),
            Node("spectralHom_real", "Agreement with real CFC", "For every globally continuous real function f, applying spectralHom to its complex-valued restriction to [0,1] gives the actual real cfc f C. Mathlib's real-to-complex CFC compatibility proves this equality. In particular it applies to every real overlap cutoff min(x,t(1-x)).", true),
            Node("spectralHom_commutes", "Range in the full commutant", "If C commutes with a bounded operator T, every spectral moment commutes with T, since C is self-adjoint. Applying this to each actual represented algebra element puts all moments in the genuine represented commutant.", true),
            Node("momentMap", "Actual continuous coefficient outputs", "Compose the spectral homomorphism with the existing continuous GNS coefficient functional a -> <Omega,Phi(g) pi(a) Omega>. This is a complex-linear map from all complex continuous interval functions to the actual continuous dual of the input algebra. Continuity in a comes from the existing operator-norm coefficient estimate.", false),
            Node("spectralFamily", "The original pair's constructed family", "Suppose C is a positive contraction in the represented commutant and its two actual coefficient functionals at C and I-C are rho and sigma. The constructed moment map is positive, since spectralHom preserves positivity and coefficient_nonneg_iff preserves operator positivity on the commutant. Unitality gives rho+sigma; the proved first moment gives rho. These prove membership in the existing full continuous-moment Family rho sigma. No Family, positive-map lift, representation normality, normalization, support condition or optimizer is assumed.", false),
            Node("spectralFamily_moment", "Exact real overlap identification", "Every continuous real f has spectral family moment equal to the actual GNS coefficient of cfc f C, as an equality of complex-linear functionals. The equality is consumed for every positive-threshold overlap in SpectralCentralizerEquality.", true),
            Paragraph(Text("The CFC and coefficient ingredients are existing library results. The construction supplies the fixed-pair spectral family; general positive operator moment lifting and the necessary direction of the localized-centralizer classification are separate mathematical questions."))
        )));

    private static DocumentBlock Node(string name, string title, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("gnsspectralmoments-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
