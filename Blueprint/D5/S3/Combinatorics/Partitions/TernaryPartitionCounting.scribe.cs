using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class TernaryPartitionCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/TernaryPartitionCounting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/akella2026genuine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective mergers transport arbitrary weighted ternary partition sums, yielding the four-party coefficient cancellation for every sign-representative family.",
        H("Ternary partition transport and four-party counting"),
        Blocks(
            Paragraph(Text("The structural counting proof uses TernaryPartitionOrbit to classify nonzero anchored ternary colourings modulo sign. A merger is any surjection between anchored label sets; its source anchor need not map to its target anchor. Factorization through its fibres, followed by subtracting the target-anchor colour, gives precisely the compatible source partitions. The merger sum therefore counts each compatible equality partition once.")),
            Paragraph(Text("Akella and Gadde, arXiv:2610.27080v1, Section II Eqs. (7)–(9) and Appendix A, give an odd-replica rank formula whose n=3 specialization also implies the four-party entropy collapse. Restoring n^{−(q−2)}, explicitly omitted at their Eq. (2), gives the normalization used by StabilizerMultiEntropyCollapse. This is a structural formal proof and reusable library for an existing conclusion, with no new unique-solve or global-priority claim. The counting question in arXiv:2607.06050v2 Section 6 is historical source text.")),
            Describe.Lean(DescribeId.Create("anchored-partition"), DeclarationHandle.Create(Prefix + "partition"),
                H("The equality partition of an anchored mode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The setoid kernel of the zero-anchored ternary colouring on Option α."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pulled-partition"), DeclarationHandle.Create(Prefix + "pullPartition"),
                H("Pulling a target partition back through a merger"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The kernel of the anchored target colouring composed with the merger map."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("separation-matrix"), DeclarationHandle.Create(Prefix + "cutPattern"),
                H("The four-label separation matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Boolean entry at i,j records whether the two ternary colours differ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinate-colour"), DeclarationHandle.Create(Prefix + "colourValue"),
                H("Coordinate colours with the last label anchored at zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For q labels, coordinates Fin(q−1) carry the ternary mode values and the last label has colour zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pair-mergers"), DeclarationHandle.Create(Prefix + "pairMergers"),
                H("The six pair mergers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The six surjections merge AB, AC, AD, BC, BD and CD respectively."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("singleton-cuts"), DeclarationHandle.Create(Prefix + "singletonCuts"),
                H("The four singleton cuts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The four surjections split ABC:D, ABD:C, ACD:B and BCD:A respectively."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("balanced-cuts"), DeclarationHandle.Create(Prefix + "balancedCuts"),
                H("The three balanced cuts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The three surjections split AB:CD, AC:BD and AD:BC respectively."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-sum"), DeclarationHandle.Create(Prefix + "partitionSumR"),
                H("Weighted separation matrices at normalized arity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For r free coordinates, sum an arbitrary real weight of each induced four-label separation matrix over the chosen finite representative family and merger into r+1 labels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("merger-transport"), DeclarationHandle.Create(Prefix + "merger_sum_transport"),
                H("Transport through arbitrary surjective mergers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary index types α and β, choose finite sets Pα and Pβ excluding zero and containing exactly one of u and −u for each nonzero mode. For every surjection m : Option α → Option β and every weight f into an additive commutative monoid, summing f over pulled-back target representatives equals its sum over source representative partitions containing ker(m). There is no finiteness assumption on the index types themselves and no condition m(none)=none. Injectivity uses sign-representative uniqueness; surjectivity uses quotient factorization and reanchoring. This theorem is consumed by the encoding bridge in result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-party-counting"), DeclarationHandle.Create(Prefix + "result"),
                H("Arbitrary-weight four-party ternary counting"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any opposite-pair representative families in arities three, two and one and any real weight on the four-by-four Boolean separation matrix, the full sum minus the six pair-merger sums plus twice the four singleton-cut sums plus the three balanced-cut sums is zero. A finite catalogue covers all fifteen four-label equivalence relations. At each nonconstant ternary partition, the coefficients cancel; the discrete partition cannot occur because four labels use only three colours, and excluding zero removes the indiscrete partition. The finite catalogue normalizes only these four-point coefficients; it is not a general Möbius formula or a Coxeter identification. Arbitrary weighted mode sums are connected to those coefficients by merger_sum_transport. StabilizerMultiEntropyCollapse.partition_count applies this result to its original thirteen, four and one concrete representatives, and the existing rank and entropy tail then gives the n=3 four-party relation. Other replica counts and party counts are outside this conclusion."))), DescribeRole.Theorem))));
}
