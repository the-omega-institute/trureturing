using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairLowArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairLowArithmetic." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual low roots and full necessary divisibility", H("Actual low roots and full necessary divisibility"),
        Blocks(
            Paragraph(Text("Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. These are scoped implementation and normal-admission materials. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open. Unfinished escape audits are disclosed in linked issue #28398.")),
            Item("actual-low-root", "actual_low_root", "Actual integrality forces root two or three", "Every a>=5 and both tails at least a are retained, with arbitrary distinct graph primes. The true full-operator eigenvector and actual graph lift supply the integer root."),
            Item("actual-divisibility", "actual_divisibility", "Full low-root divisibility disjunction", "The two divisors a-1 and a-2 and constants 3 and 20 are necessary conditions only. There is no ordering between the two tails."),
            Item("large-tail-low", "large_tail_low", "Strict low-root cutoff including boundary equality", "Both real tails may equal 2a-2. A full-operator eigenpair lies strictly between one and three; the principal minor is used only to obtain a genuine full eigenvector.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairRootArithmetic")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/PairFourEndpoints"))]));
}
