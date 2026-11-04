using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class PlaneWordEndpointCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The endpoint fiber of signed coordinate words is a product of two fixed-size subset fibers.",
        H("Exact endpoint count for signed coordinate words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("plane-word-endpoint-count"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/PlaneWordEndpointCount.endpoint_card"),
                H("Two independent position subsets give the two binomial factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A length-L word is a function from Fin L to Fin 4. The four letters are exactly the existing BajnokBeattyFirstReturnDefect.step values (1,0), (-1,0), (0,1), and (0,-1), and endpoint is their integer-plane sum. Let L,a,b be natural numbers and x,y integers. If L-2a=x+y and L-2b=x-y, with all natural numbers cast into the integers in these two equations, the number of words with endpoint (x,y) is choose(L,a) choose(L,b).")),
                    Paragraph(Text("Under the coordinate change (x,y) to (x+y,x-y), the four letters become (+1,+1), (-1,-1), (+1,-1), and (-1,+1). Record a subset S of positions where the first transformed sign is negative, and a subset T where the second sign is negative. Conversely, the two membership tests at each position recover its unique letter. The proof constructs this word-to-subset-pair equivalence and proves both inverse laws.")),
                    Paragraph(Text("The two transformed endpoint coordinates are L-2|S| and L-2|T|. Thus the given endpoint fiber corresponds exactly to pairs with |S|=a and |T|=b. Mathlib's Fintype.card_finset_len supplies the cardinalities of these fixed-size subset types, and Nat.card_prod multiplies them. The subset count is directly reused rather than reproved. No reachability or parity assumption is implicit beyond the two displayed integer equations; when a size exceeds L, its subset fiber and binomial coefficient are both zero.")),
                    Paragraph(Text("The concrete consumer is BajnokBeattyShortReturnBand.short_return_band. For length L=n+2r and endpoint (n,0), take a=b=r to obtain choose(L,r)^2. For endpoint (-n,0), take a=b=n+r and use binomial symmetry to obtain the same square. The general interface also permits other endpoints without a new counting construction. This is the classical square-lattice word count, organized here as a checked equivalence for the repository's existing four-step definitions; no literature novelty is claimed."))),
                DescribeRole.Theorem))));
}
