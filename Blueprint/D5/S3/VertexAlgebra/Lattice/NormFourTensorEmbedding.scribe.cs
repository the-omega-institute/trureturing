using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourTensorEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual minus-one product injects the algebraic tensor product of the norm-four vacuum representation and its full production commutant into the lattice carrier.",
        H("The Actual Norm-Four Tensor Embedding"),
        Blocks(
            Paragraph(Text("Let D be the production lattice data, a a charge with bilinear(D,a,a)=4, and s a complex scalar with s squared equal to one. "
                + "Let S be exactly NormFourVacuumIrreducible.vacuumDescendants(D,a,s), the span of all finite negative Virasoro words on the actual vacuum. "
                + "Let C be exactly NormFourCommutant.space(D,a,s), the subspace of the full Carrier(D) annihilated by every nonnegative coefficient of the norm-four state e. "
                + "Use the genuine inherited state-field algebra V=NormFourVacuumVertexAlgebra.vertexAlgebra(D,a,ha,s,hs) on this same S. "
                + "The tensor product throughout is the algebraic complex tensor product, so its elements are finite sums of pure tensors.")),
            Describe.Lean(
                DescribeId.Create("normfour-actual-tensor-product-map"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourTensorEmbedding.tensorMap"),
                H("The c-left actual minus-one product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex-linear map F:S tensor C to Carrier(D) is defined by F(u tensor c)=Y(c)_(-1)u, "
                    + "with the actual subtype inclusions into the production carrier. Bilinearity is inherited from the actual state-field map and its coefficients. "
                    + "The order places the commutant state c on the left of the field coefficient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfour-actual-injective-tensor-intertwiner"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourTensorEmbedding.actual_tensor_embedding"),
                H("Injectivity, every state and integer coefficient, and the complete vacuum line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all production D,a,s under the two displayed equations, F is injective. "
                    + "For every u in the whole S, every integer p and every tensor z, "
                    + "F((V(u)_p tensor id_C)z)=Y(u)_p F(z). For every c in the whole C, F(V.vacuum tensor c)=c in the actual carrier. "
                    + "The pure-tensor formula holds for all u and c. No positivity, rootlessness, PBW basis, independence of vacuum words, "
                    + "finite dimension of C, abstract Ising identification or injectivity premise is imposed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The equality of the literal generator annihilator with the full S-state commutant gives Y(u)_j c=0 "
                + "for every u in S and every natural j. In the actual mode commutator [Y(u)_p,Y(c)_(-1)], "
                + "each term has the state Y(u)_j c and therefore vanishes. This proves the full intertwining identity by tensor linearity. "
                + "In particular F intertwines every axis mode L_m, including L_0 and all positive modes.")),
            Paragraph(Text("Each tensor has a finite decomposition into natural L_0 eigencomponents, obtained from the existing finite word-grade decomposition of S. "
                + "Mapping these components through F gives actual ambient eigencomponents. The finite spectral-component theorem for the invariant subspace zero "
                + "places every component of a kernel tensor back in the kernel. A nonzero kernel would consequently contain a nonzero eigen-tensor of least natural grade n.")),
            Paragraph(Text("Choose a vector-space basis of C solely as a proof tool. Mathlib's equivFinsuppOfBasisRight identifies S tensor C "
                + "with finitely supported S-valued coordinates. Every axis mode acts coordinatewise. A nonzero positive-mode image of the least-grade kernel tensor "
                + "has a nonzero coordinate; the existing eigen_in_grade theorem makes its weight n-m a natural grade. It would be a strictly lower nonzero homogeneous kernel tensor, "
                + "a contradiction. Thus every positive mode kills every coordinate of the least-grade tensor. "
                + "Any nonzero coordinate is an actual highest-weight vector of natural weight n. The existing highest_weight_values theorem restricts its weight "
                + "to zero, one sixteenth or one half; naturality forces n=0.")),
            Paragraph(Text("All grade-zero coordinates are multiples of the actual vacuum. The finite inverse coordinate sum therefore expresses the tensor "
                + "as V.vacuum tensor c for a single c in C. Actual creation gives F(V.vacuum tensor c)=c, so a kernel tensor on this line is zero. "
                + "This contradicts the chosen nonzero tensor and proves injectivity. No completion, tensor vertex-algebra structure or analytic realization is involved.")),
            Paragraph(Text("The finite spectral and highest-weight inputs belong to NormFourVacuumIrreducible and NormFourHighestWeight. "
                + "The restricted coefficients and vacuum line belong to NormFourVacuumVertexAlgebra, while the all-state commutant equality belongs to NormFourFullCommutant. "
                + "The coordinate equivalence is Mathlib's tensor-product basis theorem; the chosen basis is not a hypothesis. "
                + "The lattice fields follow Bakalov-Kac, math/0402315, section 4.1. The norm-four state retains Shimakura, arXiv:1202.6107, (1.3), "
                + "and Dong-Mason-Zhu, Theorem 6.3 attribution. Imported residue sources retain their Carnahan and Matsuo-Nagatomo attribution and license notices. "
                + "This is a derivation for the literal production carriers, without a literature novelty claim. "
                + "It asserts no rationality, fusion, Baby Monster, Monster, CFT, string-theory or AdS/CFT completion.")))));
}
