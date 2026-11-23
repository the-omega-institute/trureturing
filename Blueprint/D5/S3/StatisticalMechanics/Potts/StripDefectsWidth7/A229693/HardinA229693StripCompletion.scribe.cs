using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693;

internal sealed class HardinA229693StripCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enumerate row completions that spend exactly a given budget.",
        H("Exact-cost row completions"), Blocks(
            Definition("matchCost", "Cost of a colour match",
                "An absent colour costs zero. A present colour costs one exactly when it agrees with the current colour."),
            Definition("completionCost", "Cost of a completion",
                "Sum the initial match, when a previous colour is supplied, the matches between neighbours, and the matches against the optional boundary colours."),
            Definition("completionRows", "Pruned completion list",
                "Try the three available colours in order, keep each head whose cost fits the budget, and prepend it to the completions at the remaining budget. The last cell must spend the entire remaining budget."),
            Theorem("completionRows_count", "Multiplicity of qualifying rows",
                "The number of listed completions passing a Boolean test equals the sum of its indicators over all rows of exactly the given cost."),
            Definition("completionCodes", "Pruned list in base three",
                "Run the same recursion on a list of boundary colours. Prepending a colour x replaces the tail code c with x plus three times c."),
            Theorem("rowCode_cons", "Code of a row with a new head",
                "The leading cell is the least significant digit of the code."),
            Theorem("completionCodes_eq", "Agreement of the two lists",
                "The numeric enumerator returns the codes of the pruned completion list in the same order."))));

    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock Theorem(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(declaration.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
