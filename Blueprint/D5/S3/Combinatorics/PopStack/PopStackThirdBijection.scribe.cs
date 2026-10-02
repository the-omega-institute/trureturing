using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackThirdBijectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackThirdBijection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The map undoPhi(n,p) is empty for n = 0 and equals 3142 for n = 4. Otherwise, when p starts with two, delete that entry and decrease every remaining value other than one to obtain q. If q is simple, apply Phi(n-1,q), increase all values, and insert one second; if not, delete its third entry and decrease every value other than one, inflate the first entry of the resulting skeleton by 21, increase all values, and insert one second. When p does not start with two, delete its third entry and subtract one from every remaining value to obtain q. If q is simple, increase its values and insert one second. If q = R(n-1), do this to B(n-1) instead. Otherwise delete the second entry of q, standardize above its third value, inflate the first entry by 21, increase all values, and insert one second.",
        H("The reverse third-position construction"),
        Blocks(
            Node("pop-stack-popstackthirdbijection-phi", "The recursive third-position construction", "Phi",
                "The map Phi(n,p) is empty for n = 0 and equals 2413 for n = 4. Otherwise delete the second entry and subtract one from all remaining values to obtain q. If q is simple with minimum third, apply undoPhi(n-1,q), increase every value other than one, and prepend two. If q is simple with minimum elsewhere, increase its values and insert one third. If q = B(n-1), return Y(n). Otherwise let s = deflateFirst(q): if its minimum is second, inflate its second entry by 12, increase every value other than one, and prepend two; if not, inflate its second entry by 21, increase all values, and insert one third.", DescribeRole.Definition),
            Node("pop-stack-popstackthirdbijection-undophi", "The reverse third-position construction", "undoPhi",
                "The map undoPhi(n,p) is empty for n = 0 and equals 3142 for n = 4. Otherwise, when p starts with two, delete that entry and decrease every remaining value other than one to obtain q. If q is simple, apply Phi(n-1,q), increase all values, and insert one second; if not, delete its third entry and decrease every value other than one, inflate the first entry of the resulting skeleton by 21, increase all values, and insert one second. When p does not start with two, delete its third entry and subtract one from every remaining value to obtain q. If q is simple, increase its values and insert one second. If q = R(n-1), do this to B(n-1) instead. Otherwise delete the second entry of q, standardize above its third value, inflate the first entry by 21, increase all values, and insert one second.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
