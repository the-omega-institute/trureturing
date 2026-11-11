using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaKernelBinsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaKernelBins.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal Identities for the Actual Kernel Bins",
        H("Universal Identities for the Actual Kernel Bins"),
        Blocks(
            Node("binCount", "The literal kernel-bin count", DescribeRole.Definition,
                "A_j is the integer cardinality of the native units u in the actual character kernel K with floor(4 val(u)/r)=j."),
            Node("bin_identities", "The two universal bin identities", DescribeRole.Theorem,
                "For every prime r greater than five congruent to five modulo eight, 5k=-3(A0-A3)-(A1-A2) and 5t=-(A0-A3)+3(A1-A2). The real parts of the literal quarter and half character sums are computed by kernel indicators and negation, then combined with the universal complex interval identities. The finite checker is not a premise."),
            Paragraph(Text("Historical source credit: Haobo Ma and Wenlin Zhang, CC BY 4.0, including the unique verification ZIP; Joseph S. Farland/OEIS sign attribution, joint Ma-Merca-Zhang application and classical class-number sources remain credited. No novelty, priority, author-consent or publication claim. Source-owner audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629; these author proofs do not replace independent whole-result acceptance.")))));
    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("merca-kernel-bins-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);
}
