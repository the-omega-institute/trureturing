using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class PositiveMarginalMatrixCompositionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition.";
    private static readonly LibraryNoteRef Note =
        LibraryNoteRef.Create("D5/L/QuantumStates/barnumhilgert2019spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global positive trace-preserving marginals and product spanning determine the joint size and the actual commuting Jordan embeddings on full complex Hermitian matrix carriers.",
        H("Positive binary marginals on full Hermitian matrices"),
        Blocks(
            Paragraph(Text("Each H(n) is the full real vector space of n by n complex Hermitian matrices with its PSD cone, canonical unscaled trace and trace pairing. The assumptions of Library equation (15) are Marginals and Spans. M is positive and real bilinear. Both real-linear marginals are positive on the whole joint cone and preserve trace on all vectors. Their readbacks on M(x,y) are tr(y)x and tr(x)y on all real vector inputs. Spans means real linear spanning by all prepared products.")),
            Law("orthogonal-preparations", "frame_orthogonal", "Orthogonal preparations before spanning",
                "The M-preparations of distinct pairs from any two orthonormal rank-one frames have zero matrix product. The adjoint effects of the two actual marginals read the local labels deterministically on the prepared states.",
                DescribeRole.Theorem),
            Law("rank-lower-bound", "rank_lower_bound", "Joint size bound from readback",
                "The joint matrix size d is at least the product ab of the local matrix sizes. The orthogonal prepared supports each contribute a nonzero direction. The hypothesis is Marginals.",
                DescribeRole.Theorem),
            Law("exact-rank-and-dimension", "rank_dimension", "Exact joint rank and real dimension",
                "With Spans as well, d = ab and dim_R H(d) = dim_R H(a) dim_R H(b), as in (18). The linearization of M is onto. The dimensions of full Hermitian matrix spaces are the squares of their matrix sizes, which gives the opposite bound.",
                DescribeRole.Theorem),
            Law("preparation-unit", "prep_unital", "The actual preparation preserves the product unit",
                "M(I,I) is the joint identity after completing the prepared product frame. The saturated frame consists of mutually orthogonal trace-one rank-one projections.",
                DescribeRole.Theorem),
            Law("rank-one-preparation", "prep_rank_one_preserver", "The actual M preserves rank one",
                "M(x,y) has matrix rank one for any rank-one Hermitian x and y. This includes signed rank-one inputs. Applying prep_rank_one to positive trace-one rank-one inputs gives a positive trace-one rank-one product.",
                DescribeRole.Theorem),
            Law("positive-adjoint", "effect_pos", "Global positivity of the trace adjoint",
                "For a real-linear marginal positive on the entire PSD cone, its adjoint for the canonical trace pairing is positive on every PSD input.",
                DescribeRole.Theorem),
            Law("unital-adjoint", "effect_unital", "Trace preservation gives a unital adjoint",
                "When the marginal preserves the canonical trace on all vectors, its trace adjoint sends the local identity to the joint identity.",
                DescribeRole.Theorem),
            Law("left-adjoint-injective", "effect_injectiveA", "The left adjoint is injective",
                "With a nonzero right matrix carrier, a trace-one spectator and the left preparation readback give injectivity of the actual left marginal adjoint.",
                DescribeRole.Theorem),
            Law("right-adjoint-injective", "effect_injectiveB", "The right adjoint is injective",
                "With a nonzero left matrix carrier, the right preparation readback gives injectivity of the actual right marginal adjoint.",
                DescribeRole.Theorem),
            Law("actual-matrix-product", "effect_mul", "The marginal adjoints multiply to the preparation",
                "For all local Hermitian x and y, the ordinary matrix product of the two marginal adjoint images equals the matrix underlying M(x,y). The product-frame identity extends to all vectors by spectral expansion.",
                DescribeRole.Theorem),
            Law("matrix-commutation", "effect_commute", "The actual adjoint ranges commute as matrices",
                "The left adjoint image of every x commutes with the right adjoint image of every y in the ambient complex matrix algebra.",
                DescribeRole.Theorem),
            Law("left-jordan", "effect_jordanA", "The left adjoint preserves Jordan multiplication",
                "The left adjoint preserves the symmetrized product (XY+YX)/2 on the whole left carrier. The joint frame gives its square law, and polarization gives its Jordan law.",
                DescribeRole.Theorem),
            Law("right-jordan", "effect_jordanB", "The right adjoint preserves Jordan multiplication",
                "The right adjoint preserves the same symmetrized product on the whole right carrier.",
                DescribeRole.Theorem),
            Law("ambient-jordan-commutation", "effect_jordan_commute", "The two Jordan multiplication operators commute",
                "The Jordan multiplication operators of the two adjoint images commute on every joint Hermitian input z, as required by (16).",
                DescribeRole.Theorem),
            Law("actual-jordan-product", "effect_product", "The Jordan effect product is the actual preparation",
                "For all f and g the Jordan product of the two marginal adjoint images equals M(f,g). This identifies N in (16) using the canonical trace pairing.",
                DescribeRole.Theorem))));

    private static DocumentBlock Law(string id, string selector, string heading, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + selector),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Note),
            Blocks(Paragraph(Text(explanation))), role);
}
