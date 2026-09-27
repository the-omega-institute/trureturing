using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class ZeroRunWordGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete intervals and actual transport parity of binary gap words.",
        H("Zero-Run Word Geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-iff-interval"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry.complete_iff_interval"),
                H("Complete candidates are exactly the positive gaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite list ls of natural zero-gap lengths and starting position p, ones ls "
                            + "p places a one at p and then advances by l+1 across each gap. Every other physical "
                            + "position is zero. A complete zero interval (a,b) has one endpoints, a+2 <= b, and no "
                            + "interior one. The theorem identifies these concrete intervals exactly with intervals "
                            + "ls p. Zero gaps contribute no candidate.")),
                    Paragraph(Text(
                        "The forward implication finds the next actual one after a; any later endpoint would "
                            + "leave an interior one and violate completeness. The reverse implication checks the "
                            + "endpoints and every interior position. This exhausts all candidates, including each "
                            + "individual length-one filler; it does not assume a supplied queue is complete."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ones-geometry"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry.ones_geometry"),
                H("Position bounds and number of one endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every ls and p, all one positions lie between p and p+span ls, where span ls is "
                            + "the sum of l+1 over the gaps. There are exactly length ls + 1 distinct one "
                            + "positions, and both endpoints occur. Nonnegative gaps give a strictly positive "
                            + "advance between successive ones, including when a gap is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transport-suffix"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry.transport_suffix"),
                H("Transport counts every consumed zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary lists pre and post, let b=p+span pre and e=b+span post+1+n. The "
                            + "transport from the vertex after the closing one b to the current vertex e is the "
                            + "parity of all zero positions in the open interval (b,e). The theorem proves this "
                            + "equals (sum post+n) mod 2.")),
                    Paragraph(Text(
                        "The one positions in that interval are exactly the suffix one positions with the "
                            + "anchor b removed. Subtracting their count from the interval length counts all zeros, "
                            + "including zeros in fillers that a selector discards. The right endpoint e is "
                            + "excluded because its input has not yet been read."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interval-geometry"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry.interval_geometry"),
                H("Interval bounds and concatenation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every interval (a,b) contributed by ls starts at or after p, has positive interior "
                            + "length, ends by p+span ls, and has interior length belonging to ls. Concatenating "
                            + "any second list ys gives exactly the union of the first intervals and the intervals "
                            + "of ys starting at p+span ls. Shared one endpoints are permitted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("family-head-dominates"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/ZeroRunWordGeometry.family_head_dominates"),
                H("Descending long runs dominate later gaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "familyGaps r h begins with the long gap 2r+3 and, for r>0, continues with 2h(0) gaps "
                            + "of length one and the recursively shorter family. At r=0 it is the single gap of "
                            + "length three. The first complete interval (p,p+2r+4) occurs, and every other "
                            + "interval has strictly smaller interior length.")),
                    Paragraph(Text(
                        "The statement is uniform in r and the entire natural-valued parameter function h. It "
                            + "includes empty filler segments and arbitrary filler sizes. With r=q-1 these are the "
                            + "long lengths 2q+1,2q-1,...,3."))),
                DescribeRole.Theorem))));
}
