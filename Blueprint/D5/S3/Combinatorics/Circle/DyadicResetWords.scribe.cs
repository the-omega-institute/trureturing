using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class DyadicResetWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realizing allocated coins as actual legal reset words.",
        H("Realizing allocated coins as actual legal reset words"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-dyadicresetwords"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/DyadicResetWords.word_of_allocation"),
                H("Realizing allocated coins as actual legal reset words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let S be a finite physical set of positive labels with f(a)=2^e(a), and let Z be an actual list of reset labels of value -M. For a natural tail h<=M, an Allocation into one capacity-M bin per occurrence of Z and one capacity-h tail produces a word V permuting S.toList++Z and satisfying InStrip(f,M,0,V). The construction concatenates each allocated positive list with its own actual reset occurrence and then the tail. Empty bins and a zero tail are included.")),
                    Paragraph(Text("Positive monotonicity bounds every interior prefix by the exact bin endpoint. Each reset returns M to zero, and every tail prefix stays between zero and h. Physical disjointness of the allocation and the original reset list is retained through the permutation; it is never replaced by an inventory of numerical values.")),
                    Paragraph(Text("allocation_of_strip derives the old positive set, actual reset list, endpoint and allocation from an arbitrary Nodup legal word using reset_decomposition. replace_bin removes a physical subcollection from a single bin and replaces it by a fresh coin of exactly its total, preserving all capacities. replacement_perm proves the exact returned/inserted physical permutation. top_occupancy counts each original top label exactly once and bounds a bin below twice the top denomination by one top occurrence; missing_top_bound supplies the exhaustive native case split."))),
                DescribeRole.Theorem)), []));
}
