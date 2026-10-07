using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DyckValleys;

internal sealed class ValleyBargraphDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DyckValleys/ValleyBargraphDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "State Mu–Welker's Conjecture 3.9: UUDD-avoiding Dyck paths with i valleys are counted by bargraphs of semiperimeter n and width i.",
        H("Mu–Welker Dyck valleys and bargraph statement"),
        Blocks(
            Node("avoids-uudd", "The source-side UUDD-avoidance predicate", "AvoidsUUDD is the maximal-face condition from the source's Lemma 3.4: a Dyck word contains no factor UUDD."),
            Node("valleys", "Valleys count adjacent DU factors", "The valleys predicate counts adjacent DU factors in the Dyck word."),
            Node("ascent", "The total ascent of a height list", "The ascent of a height list is the sum of the positive successive height differences."),
            Node("semiperimeter", "The bargraph semiperimeter", "The semiperimeter is length plus the first height plus the total ascent."),
            Node("is-bargraph", "Positive column-height lists are bargraphs", "A bargraph is a nonempty list whose column heights are all positive."),
            Describe.Lean(
                DescribeId.Create("conjecture-three-nine"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The Mu–Welker counting conjecture"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n ≥ 2 and 1 ≤ i ≤ n − 1, the finite set of UUDD-avoiding Dyck words of semilength n with i valleys has the same cardinality as the finite set of bargraph height lists of length i and semiperimeter n. This file records the exact open target; it does not claim that the target is already resolved."))),
                DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create("mu-welker-defs-" + id),
            DeclarationHandle.Create(Prefix + DeclarationName(id)),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static string DeclarationName(string id) => id switch
    {
        "avoids-uudd" => "AvoidsUUDD",
        "valleys" => "valleys",
        "ascent" => "ascent",
        "semiperimeter" => "semiperimeter",
        "is-bargraph" => "IsBargraph",
        _ => throw new System.ArgumentOutOfRangeException(nameof(id)),
    };
}
