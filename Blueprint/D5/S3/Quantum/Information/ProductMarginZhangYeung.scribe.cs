using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class ProductMarginZhangYeungDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spectral gap on the actual product-margin state", H("ProductMarginZhangYeung"), Blocks(
            Describe.Lean(DescribeId.Create("actual-gap-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginZhangYeung.actual_gap_identity"),
                H("The actual spectral entropy identity"), StatementSource.FromAuthor(GapIdentity()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/codex2026productmargin")),
                Blocks(Paragraph(Text("The two LocalPair parameters contain four independent nonnegative real coordinates xC, zC, xD, zD, each pair in the closed unit disk. Coupling contains an arbitrary complex positive semidefinite K bounded by P and Q, where P is the product of the positive local members and Q is the product of the negative members. The actual density on two classical bits and two qubits has blocks (P-K)/2, K/2, K/2, (Q-K)/2. Its entries, positivity and trace normalization are retained even when a block vanishes.")),
                    Paragraph(Text("Delta is the original Zhang--Yeung combination of natural-log von Neumann entropies of actual partial traces. Its conditional information terms are 2 I(C:D|A), I(C:D|B), I(A:C|D) and I(A:D|C), with I(A:B)-I(C:D). The two row and column marginals are uniform pointer records of P and Q. Pointer orthogonality gives the cq entropy formula without imposing orthogonality on the prepared qubits or normalizing a zero-weight block. The AB entropy is log(2)+h(Re Tr K), including both endpoints.")),
                    Paragraph(Text("The right side uses the actual symmetric local Holevo entropies and the mutual information of M=(P+Q)/2. Establishing nonnegativity requires the information estimates for the actual prepared states in addition to this identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-zhang-yeung-nonnegative"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ProductMarginZhangYeung.actual_zhang_yeung_nonneg"),
                H("The four-parameter product-margin inequality"), StatementSource.FromAuthor(Nonnegative()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/codex2026productmargin")),
                Blocks(Paragraph(Text("For every two independent closed-disk LocalPair parameters and every complex positive common lower matrix K, the original spectral Zhang--Yeung gap of the actual density is nonnegative. No information estimate, commutation or strict positivity is an input hypothesis.")),
                    Paragraph(Text("When both x coordinates are less than one, the actual marginal reference states are faithful even if the joint density is singular. The canonical product-recovery identity identifies their mutual information with support-aware relative entropy. Local preparation channels map both each intermediate cq density and its product reference to the physical output. Their DPI bounds combine with qubit Holevo contraction, the common-trace bound and the closed-interval scalar entropy certificate. If an x coordinate equals one, the corresponding z is zero and the CD state is directly a product. Zero reliabilities, zero weights and pure prepared states remain included.")),
                    Paragraph(Text("The conclusion concerns this four-parameter classical-bit product-margin construction. It makes no assertion for arbitrary four-party quantum states or for a coordinate-free extension."))), DescribeRole.Theorem))));

    private static Formula Nonnegative()
    {
        var c = F.Id("c"); var d = F.Id("d"); var k = F.Id("k");
        return Seq(Forall, Sp, c, Comma, d, Colon, F.Id("LocalPair"), Comma, Esc,
            Forall, Sp, k, Colon, Call("Coupling", c, d), Comma, Esc,
            D(0), Le, Sp, Call("zhangYeungGap", k));
    }

    private static Formula GapIdentity()
    {
        var c = F.Id("c"); var d = F.Id("d"); var k = F.Id("k");
        var tr = Call("re", Call("trace", Call("K", k)));
        var rhs = Seq(Call("log", D(2)), Minus, Call("h", tr), Plus,
            Call("qubitHolevo", Call("x", c), Call("z", c)), Plus,
            Call("qubitHolevo", Call("x", d), Call("z", d)), Minus,
            D(3), Cdot, Sp, Call("quantumMutualInformation", Call("productMixture", c, d)));
        return Seq(Forall, Sp, c, Comma, d, Colon, F.Id("LocalPair"), Comma, Esc,
            Forall, Sp, k, Colon, Call("Coupling", c, d), Comma, Esc,
            Call("zhangYeungGap", k), Eq, rhs);
    }
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
