using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BinomialKernelDeltaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite binomial expansions cancel the charged commutator at a sufficient lattice order.",
        H("Finite Binomial Difference Cancellation"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Let V be any complex module and K an integer two-index kernel with independent lower "
                + "bounds on both coordinates. Define expansion_b(K)(k,l) as the finite sum of (-1)^j "
                + "choose(b,j) K(k-b+j,l-j), and rawDelta f(k,l)=f(k-1,l)-f(k,l-1). Finite Option(N) "
                + "splitting and signed Pascal reindexing prove the difference law.")),
            Describe.Lean(
                DescribeId.Create("binomialkerneldelta-rawdelta-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BinomialKernelDelta.rawDelta_expansion"),
                H("One difference raises the integer exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every integer b, rawDelta(expansion_b(K))=expansion_(b+1)(K). All sums have finite "
                        + "kernel support; this covers negative b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binomialkerneldelta-binomial-commutator-killed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BinomialKernelDelta.binomial_commutator_killed"),
                H("A sufficient cancellation order for the two kernel orders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("rawDelta iterated (-b).toNat kills expansion_b(K) minus integerSign(b) times "
                        + "flip(expansion_b(flip(K))). For b>=0, finite binomial reflection makes the discrepancy "
                        + "zero already. For b<0, iteration raises b to zero and both orders become the same "
                        + "kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binomialkerneldelta-delta-binomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BinomialKernelDelta.delta_binomial"),
                H("Finite normalized difference expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every two-index endomorphism distribution, natural order and integer first,second "
                        + "indices, deltaEnd^order equals the finite range sum of (-1)^offset choose(order,offset) "
                        + "times the distribution at (first+order-offset,second+offset). Commuting coefficient "
                        + "shifts prove it."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI "
                + "10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and "
                + "conformal construction. Equation numbers refer to arXiv v1.")),
            Paragraph(Text("Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue "
                + "locality and reconstruction by creative local fields, divided derivatives and nested "
                + "normal products.")),
            Paragraph(Text("Finite normal-product and integer residue kernels retain Scott Carnahan attribution: "
                + "vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, "
                + "VertexAlg/VertexBasic/VertexOperator.lean, Apache-2.0. Actual coefficient proofs are "
                + "re-elaborated on V; no polynomial Fock theorem is transferred between carriers.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}
