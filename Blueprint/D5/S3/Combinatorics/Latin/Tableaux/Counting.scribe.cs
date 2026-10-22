using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin.Tableaux;

internal sealed class CountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/Tableaux/Counting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/daugherty2026counting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal source Latin tableaux: Counting", H("Counting for Latin tableaux"),
        Blocks(
            Paragraph(Text("Daugherty et al., arXiv:2610.29291v1, Conjecture 6.3 asks for the full count of Latin tableaux of shape (k,k-1,...,5,4,3,3) for every integer k at least five. Cells and integer symbols retain their fixed identities, and the prescribed symbol multiplicities are those of the conjugate partition.")),
            Describe.Lean(DescribeId.Create("latin-counting-columndisjoint"),
                DeclarationHandle.Create(Prefix + "ColumnDisjoint"), H("Literal column compatibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Compare entries only at the same actual column index, allowing absent cells in shorter rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-counting-rawlatin"),
                DeclarationHandle.Create(Prefix + "RawLatin"), H("Actual row lists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Each row is a permutation of its exact initial symbol interval, and all row pairs satisfy column compatibility."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-counting-available"),
                DeclarationHandle.Create(Prefix + "available"), H("Availability for the next longest row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At each fixed column retain exactly those symbols not already present there."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-counting-enumerate"),
                DeclarationHandle.Create(Prefix + "enumerate"), H("Complete finite enumeration"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Recursively prepend every matching of the actual availability graph to every smaller tableau. Distinct tails give disjoint extension sets."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-counting-mem-enumerate"),
                DeclarationHandle.Create(Prefix + "mem_enumerate"), H("Enumeration is exact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Proves both directions between enumeration membership and literal compatible row permutations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-rowsof"),
                DeclarationHandle.Create(Prefix + "rowsOf"), H("The zero-based row representation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Read all finite-source rows in their actual order, with zero-based values; the source equivalence restores actual integer labels by adding one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-counting-enumerationequiv"),
                DeclarationHandle.Create(Prefix + "enumerationEquiv"), H("Every source filling appears exactly once"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The explicit inverse row construction composes with sourceEquiv, producing a reversible bijection from all source tableaux to enumeration members."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-counting-source-enumeration"),
                DeclarationHandle.Create(Prefix + "source_enumeration"), H("Equality of literal counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The algorithm counts exactly the unrestricted source tableaux, with no isotopy, reduction, or symmetry identification."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-shape-succ"),
                DeclarationHandle.Create(Prefix + "shape_succ"), H("Actual shape growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every k at least five the next source diagram is obtained by prepending its actual row of length k+1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-base-count-and-invariant"),
                DeclarationHandle.Create(Prefix + "base_count_and_invariant"), H("The complete base at k=5"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Kernel decision checks all tableaux of (5,4,3,3): there are 144, and every one has the full next-row invariant with low symbols {0,1,2} and high symbols 3,4,5. The smaller (4,3,3) layer cannot supply a uniform fourfold transition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-universal-invariant"),
                DeclarationHandle.Create(Prefix + "universal_invariant"), H("No missing induction hypotheses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Induction proves the full invariant for every tableau at every k at least five. The availability-update identity is proved using actual row bounds. No transition, invariant, enumeration, or coverage assumption is left in the result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-count-step"),
                DeclarationHandle.Create(Prefix + "count_step"), H("Exactly four extensions for every tableau"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every invariant graph has four distinct matchings; prepending to different tails gives disjoint sets. This proves the count recurrence rather than assuming it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-conjecture63"),
                DeclarationHandle.Create(Prefix + "conjecture63"), H("The complete universal count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural k at least five, the full source count is 9 times 4 to the power k-3. The proof combines the exact source bijection, checked complete base, and proved all-parameter transition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-counting-conjecture63-integer"),
                DeclarationHandle.Create(Prefix + "conjecture63_integer"), H("Conjecture 6.3 over every integer k at least five"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every integer k at least five, LT of its natural value is 9 times 4 to the power k.toNat-3. In this domain conversion is exact, and the shape is precisely the source shape. This is the full source assertion, not a bounded check or weaker existence statement."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("daugherty-latin-tableaux-conjecture63"), ResolutionKind.Proved))), []));
}
