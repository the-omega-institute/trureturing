using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeMajorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On each positive-real fixed-sum plane the order-three scalar expression is strictly Schur-convex. Among comparable triples equality occurs exactly for permutations. This does not assert that incomparable triples have different values, or that real scalar sizes are physical fractional modes.",
        H("Strict Schur comparison of positive scalar triples"),
        Blocks(
            Paragraph(Text("The finite balancing law is from Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. The majorization criterion is classical (Marshall, Olkin and Arnold); the physical family is due to Camargo and Nishida. The existing PositiveSimplexGeometryAndMixing and LogScalarCurvatureMonotone modules supply the positive T-transform chain, and retain their existing authorship and audit boundaries.")),
            Describe.Lean(DescribeId.Create("gaussian-three-schur-comparison"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeMajorization.schur_comparison"),
                H("Majorization, strictness and permutation equality"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("V"), Open, F.Id("k"), Comma,
                    F.Id("x"), Close, Le, Sp, F.Id("V"), Open, F.Id("k"), Comma,
                    F.Id("y"), Close, Semi,
                    F.Id("V"), Open, F.Id("k"), Comma, F.Id("x"), Close, Eq,
                    F.Id("V"), Open, F.Id("k"), Comma, F.Id("y"), Close,
                    Sp, Iff, Sp, Exists, Sp, SigmaLower, InMacro, Sp, F.Id("Perm"), Open,
                    OpenBrace, D(0), Comma, D(1), Comma, D(2), CloseBrace, Close, Comma,
                    F.Id("x"), Eq, F.Id("y"), Circ, Sp, SigmaLower))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k > 0 and positive real triples x and y, suppose x is more mixed than y in the standard descending-prefix-sum majorization order. This includes equality of their total sums. Then V(k,x) <= V(k,y), and equality holds if and only if x is a permutation of y. Hence non-permutation majorization gives a strict inequality. The proof normalizes the common positive sum to one and rescales k to preserve the scalar expression. The existing positive T-transform chain then reduces comparison to the proved strict pair-mixing law. Every intermediate triple stays positive; equality along the chain can contain only identity, full-swap or tied-pair steps and therefore yields a permutation. No Schur property is a hypothesis."))),
                DescribeRole.Theorem, null))));
}
