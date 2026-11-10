using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeBalancingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every proper convex mixing of unequal positive scalar coordinates strictly decreases the replica-three value. Identity, full swap and tied pairs account for exactly all equalities. Real coordinates here are a scalar extension, not fractional physical modes.",
        H("Strict pair balancing at replica three"),
        Blocks(
            Paragraph(Text("Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. The physical family is due to Camargo and Nishida; classical majorization is credited to Marshall, Olkin and Arnold.")),
            Describe.Lean(DescribeId.Create("gaussian-three-pair-mixing"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeBalancing.pair_mixing"),
                H("Pair mixing and its complete equality classification"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("V"), Open, F.Id("k"), Comma,
                    Seq(F.Id("x"), Apos), Comma, Seq(F.Id("y"), Apos), Comma, F.Id("z"), Close,
                    Le, Sp, F.Id("V"), Open, F.Id("k"), Comma, F.Id("x"), Comma,
                    F.Id("y"), Comma, F.Id("z"), Close, Semi,
                    F.Id("V"), Open, F.Id("k"), Comma, Seq(F.Id("x"), Apos), Comma,
                    Seq(F.Id("y"), Apos), Comma, F.Id("z"), Close, Eq,
                    F.Id("V"), Open, F.Id("k"), Comma, F.Id("x"), Comma, F.Id("y"), Comma, F.Id("z"), Close,
                    Sp, Iff, Sp, F.Id("t"), Eq, D(0), Sp, Lor, Sp, F.Id("t"), Eq, D(1), Sp, Lor, Sp,
                    F.Id("x"), Eq, F.Id("y")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k,x,y,z > 0 and 0 <= t <= 1, set x' = (1-t)x + ty and y' = tx + (1-t)y. Then V(k,x',y',z) <= V(k,x,y,z), with equality if and only if t = 0, t = 1, or x = y. In particular a proper mixing of unequal coordinates strictly lowers V while preserving x+y+z and positivity. The proof compares the positive logarithmic quotients at fixed x+y and z. Their cross difference factors as k^2 z (x'y' - xy) times a strictly positive polynomial; x'y' - xy = t(1-t)(x-y)^2. This establishes the local balancing law without assuming Schur convexity."))),
                DescribeRole.Theorem, null))));
}
