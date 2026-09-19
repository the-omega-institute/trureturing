using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class CyclicStackPreimagesCandidatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit even and odd candidate words are permutations in the target fibre.",
        H("Cyclic-Stack Fibre Candidates"),
        Blocks(
            Paragraph(Text(
                "The fibre is defined by filtering the complete list of permutations of "
                    + "1,...,n by equality of the actual stack output to the target. The candidate "
                    + "family is constructed separately. Its words interleave increasing high entries with increasing low "
                    + "entries and leaves one chosen gap empty. Its gap decomposition is literal: "
                    + "the even candidate has no empty gap, while an odd candidate has exactly the "
                    + "selected empty gap.")),
            Paragraph(Text(
                "The target is a permutation of the interval from one through n. Every odd "
                    + "candidate with an admissible omitted gap maps to that target, so all m+1 "
                    + "odd candidates belong to the full fibre. The even candidate does likewise, "
                    + "giving the corresponding lower bound of one.")))));
}
