using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Analysis;

internal sealed class OriginalSobolevDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hilbert and Sobolev completions of the original positive-lattice Hermitian form.",
        H("Original Hermitian Sobolev spaces"),
        Blocks(
            Paragraph(Text("Model retains LatticeData D, positive definiteness of gramReal(D), and a complex matrix H with both H*gramComplex(D)=1 and gramComplex(D)*H=1. The finite carrier is the original finite charge sum of oscillator polynomials, with its original mixed-colour Hermitian form Hm and normD=sqrt(Re Hm(v,v)). Positivity is reused from OriginalCurrentEnergy through the invertible real full frame and FactorialFockMetric; original monomials are not assumed orthogonal.")),
            Paragraph(Text("Set T=1+sugawaraMode(D,H,0). Finite(k) has literally Carrier(D) as its elements and the pulled-back inner product Hm(T^k u,T^k v). The coefficient formula for T^k multiplies a label of energy E by (E+1)^k. Nonnegativity of the original energies makes every such multiplier nonzero, proving injectivity and hence definiteness of the pulled-back form. Sobolev(k)=H_k is its Mathlib UniformSpace.Completion; Hilbert=H_0. The linear embedding of finite states is injective and dense, has norm normD(T^k v), and at order zero preserves exactly Hm.")),
            Paragraph(Text("completedGrade(k,n) is the range of the embedded original algebraic grade, without taking an additional closure. Its finite dimensionality proves that this range is already closed and complete. The orthogonal projection onto it agrees with the original gradeProjection on finite states. A finite sum of these projections is a genuine algebraic truncation even on a completed vector. Orthogonality makes truncations contractions, and density of finite states proves that the net over finite subsets of integer grades converges to each vector in every H_k.")),
            Paragraph(Text("For j<=k the original identity extends to inclusion(j,k):H_k->H_j by the monotone energy norms. These maps agree with finite embeddings, compose coherently, and commute with grade projections. Totality of the projections and their algebraic ranges prove that every inclusion is injective. OriginalModeExtension uses the norms, dense embeddings and inclusions; OriginalSmoothDomain uses their injectivity and compatibility; OriginalSmearingCore uses the algebraic convergent truncations for graph approximation and sector identification.")),
            Paragraph(Text("The module supplies consumed definitions and private proof components for original_smooth_fields, with no separate theorem Describe or independent novelty claim. Completion, bounded extension, projection and finite-dimensional closedness use Mathlib under its existing Apache 2.0 attribution. The original lattice and Hermitian-form suppliers retain their source attributions."))),
        []));
}
