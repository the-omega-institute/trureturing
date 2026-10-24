using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyOddProductDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/HeadleyOddProduct.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even R-star base times any odd finite abelian group retains its prescribed zero-row triple.", H("HeadleyOddProduct"), Blocks(
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-difference-spec"),
                DeclarationHandle.Create(Owner + "difference_spec"), H("Actual successor and difference permutations"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S is the ordinary row lift after a source three-cycle on the a,zero,b columns for each internally selected positive row. D is the old difference permutation after the inverse source three-cycle. The additive relation a+c=b proves that these are the actual labels S(v)-v in original product coordinates. Composition of equivalences supplies both inverse laws for S and D; no label inventory is a premise. The two inverse-pair paths and their six labels are attributed to Section 4 of the earlier native Headley construction and the accepted odd-row proof, not claimed as a new literature result."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-box-first-return"),
                DeclarationHandle.Create(Owner + "box_first_return"), H("The complete first positive return"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The gadget uses two steps at row zero and three steps on any other row. The ordinary tail uses M-3 steps, with its first lift T1 and the even remaining M-4 negations. Their ordered composite returns (a,h) to (a,pred(h)). No intermediate gadget vertex has first coordinate a; bounded injectivity of the base orbit excludes a from every intermediate ordinary column. The proof includes closure and the M=4 tail. This is an actual power statement about the defined successor, rather than an assumed row-return certificate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-nonzero-cycle"),
                DeclarationHandle.Create(Owner + "nonzero_cycle"), H("All row blocks form the entire nonzero orbit"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each inverse pair has paths (a,h),(0,-h),(0,h),(c,-h) and (a,-h),(b,h),(b,-h),(c,h); the zero row retains (a,0),(b,0),(c,0). The actual ordinary tail starts with T1 and then uses an even number M-4 of negations. Its complete return is predecessor. Every exceptional vertex is on one of these paths. The original base cycle enumerates every other column, and each intermediate row map is a permutation, so every ordinary fiber is reached. The predecessor cycle connects all a-rows. This proves one cycle on the entire nonzero product, with no additional component or unaccounted seam. The M=4, trivial-row and row-order-three cases remain in the same construction."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headleyoddproduct-exists-rstar-product"),
                DeclarationHandle.Create(Owner + "exists_rstar_product"), H("The full arbitrary odd-factor theorem with the exact triple"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input is an RStar on X, which includes Even(Nat.card X), and Odd(Nat.card H), for arbitrary finite additive commutative groups. The output is an RStar on X×H with a=(r.a,0), b=(r.b,0), c=(r.c,0). The proof supplies actual successor and difference permutations, fixing the origin, the entire nonzero cycle, every triple field and even cardinality. The odd factor is obtained by the original unconditional Gordon decomposition and transported back additively, preserving coefficient-one differences and zero rows. There is no generator, supplied decomposition, orthomorphism, inventory or cycle-certificate premise. The intended consumer is the odd quotient factor in the Headley extension program. The full Headley induction, full uniform finite-field route and original arbitrary-subset/same-M/original-coordinate/coefficient-one parent remain open; this theorem does not settle them."))), DescribeRole.Theorem))));
}
