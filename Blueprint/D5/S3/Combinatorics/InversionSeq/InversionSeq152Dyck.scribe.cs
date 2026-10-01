using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152DyckDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weakly increasing inversion sequences correspond to Dyck paths, with increases recorded by descent lengths.",
        H("Weakly Increasing Inversion Sequences and Dyck Paths"),
        Blocks(
            Node("inversionseq-inversionseq152dyck-east-counts", "Counts of preceding down steps", "eastCounts",
                "Starting with a nonnegative count e, traverse a word of up and down steps. Record the current count at each up step and increase it by one at each down step. The resulting list has one entry per up step.", DescribeRole.Definition),
            Node("inversionseq-inversionseq152dyck-dyck-steps", "Steps from a sequence of counts", "dyckSteps",
                "Given a size n, a current count e and a word of nonnegative integers, replace each successive value v by v minus e down steps followed by one up step, and continue with current count v. After the last value, append n minus the current count down steps. Subtractions are truncated at zero.", DescribeRole.Definition),
            Node("inversionseq-inversionseq152dyck-mono-dyck-equiv", "A bijection preserving descent statistics", "monoDyckEquiv",
                "For every nonnegative n, weakly increasing inversion sequences of length n are in bijection with Dyck paths of semilength n. The forward map inserts down steps according to successive entry counts, and the inverse records the number of down steps before each up step. The final descent has length n minus the maximum sequence entry, taking the maximum of the empty sequence to be zero. The lengths of all other nonempty descents are the positive successive differences of the sequence after adjoining an initial zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
