using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class OriginalRowBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attained minima and an actual maximal parent bound every physical own-row factor.",
        H("Uniform factors of original centered-source rows"),
        Blocks(
            Paragraph(Text("Let s(i)=centered(2^k-1,2^i*t) on Fin(k), Q=2^(k-2), and C=(2^k-2)/2. Physical advance iterates finRotate(k). An own row has a LARGE parent, a literal SMALL interior, and its next LARGE terminal. Sorting all actual LARGE offsets relative to x defines sourceParent and sourceLength. These are the existing cardinality-generic cuts, including their true boundary at k.")),
            Describe.Lean(DescribeId.Create("original-computed-row-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/OriginalRowBounds.computed_row_bounds"),
                H("A uniform length and terminal estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For natural k,t,L, integers a,b and p in Fin(k), RowCore assumes k>=2, a nonzero centered source, 0<a<=b, the negative-magnitude lower bound a, the positive lower bound b, attainment of -a, a physical maximum p, and an actual OwnRow of length L after p. For every physical LARGE x and every natural i less than the number of actual LARGE offsets from x, put l=sourceLength(t,x,i), f=2^l, and c=abs(s(advance(sourceParent(t,x,i),1))). Then l<=L, 1<=f<=2^L, and Q<=f*c<=C. The seed of an empty row is its LARGE terminal; the same estimate applies when l=0.")),
                    Paragraph(Text("An attained occurrence of -a has a positive LARGE predecessor. Maximality and the minimum bound force the successor of p to be exactly -a. The terminal of p's row therefore gives Q<=2^L*a. Every actual successor has magnitude at least a: use the negative minimum for a negative successor and a<=b with the positive minimum for a positive successor. If another own row were longer than L, its L-th doubling would still be SMALL but would have magnitude at least 2^L*a>=Q, a contradiction. The computed cut supplies this own row; its terminal magnitude is exactly f*c and the centered-source bound gives f*c<=C.")),
                    Paragraph(Text("This estimate supplies the actual dyadic factor bounds used by lower first selection, reversed pairs and staged negative/positive row advances. For a source with m LARGE occurrences of each sign, the cut count is 2m; every index below that count is covered. In particular row eight keeps its actual seed a0, which is not assumed at most z. Further residual factor classifications and each SMALL cost and LARGE gate require their own proofs. No selector, legal prefix, physical exhaustion or arbitrary-tail continuation follows from this estimate alone.")),
                    Paragraph(Text("The setting is the circle configuration problem of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. The estimate is a deduction from the centered-source recurrence and attained extrema. The cyclic action is on the physical labels; its integer coboundary conservation is compatible with this local threshold argument. Equal values, nonunits, shorter numerical orbits, cyclic shifts and repetitions retain their separate physical labels. The original negative-SMALL nonET condition is unchanged and is unnecessary for this estimate. The full conjecture and normalization remain open."))),
                DescribeRole.Theorem)), []));
}
