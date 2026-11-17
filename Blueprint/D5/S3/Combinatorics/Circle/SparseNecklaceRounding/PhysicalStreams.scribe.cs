using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.SparseNecklaceRounding;

internal sealed class SparseNecklacePhysicalStreamsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical sparse-necklace streams and thresholds",
        H("Physical sparse-necklace streams and thresholds"),
        Blocks(
            Describe.Lean(DescribeId.Create("uniform-sparse-necklace-rounding-proposition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SparseNecklaceRounding/PhysicalStreams.UniformSparseNecklaceRounding"),
                H("Full physical proposition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This defines a proposition. For all natural p>=1 and gaps:Fin(p)->Nat with every gap at least two, let k=sum gaps and e=sum_j 2^(sum_{q<j} gaps(q)). Set N=2^k-1 and H=N/2, the integer (N-1)/2. The old coordinate is actualSource(k,e); the new coordinate is actualSource(k+1,2e), whose fresh label k must have value e.")),
                    Paragraph(Text("The proposition asks for two permutations wp,wm of Fin(k). Their literal fresh-first ear words must be permutations of Fin(k+1), starting with k. Both separate coordinate totals must be zero. At every natural physical prefix q, the old sum uses wp.take(q-1) or wm.take(q-1), and the new sum uses earWord.take(q). All plus sums must be nonnegative; all minus sums must be at most H,N. Natural subtraction covers q=0, and overlength takes saturate.")),
                    Paragraph(Text("It also asks for a list of at most p-1 corner records with distinct prefix lengths and pairwise disjoint physical positive/terminal labels. Every record is a strict crossing of its specified native demand threshold inside the positive label interval. It displays wp=u++[i,j]++v and wm=u'++[j,i]++v' at physical prefix length length(u)+2=length(u')+2. Folding the literal label swaps gives wm. Every plus upper-bound failure and every minus lower-bound failure must occur at one of these positions; each finite error set over Fin(k+2) has cardinality at most the number of records. Thus the possible-corner list has exactly that many entries while actual failures may be fewer.")),
                    Paragraph(Text("The construction lists positive labels in reverse chain order and terminals in that same order. A terminal threshold strictly inside a positive interval produces a cut block. Equality produces a completed positive label followed by the terminal in both words. The expression defining the proposition includes p=1, repeated gaps and repeated coordinate values, and assumes no path feasibility, certificate, primitivity or coprimality."))),
                DescribeRole.Definition)), []));
}
