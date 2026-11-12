using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class RepeatedPairProductArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded four-prime tails, equality families and the old-method boundary.",
        H("Unbounded four-prime tails, equality families and the old-method boundary."),
        Blocks(
            Paragraph(Text("The same PR9 repeated-pair-product-tail source supplies these exact identities. All real a>=2 and all boundary parameters are included. For four arbitrary distinct primes and all positive integer a,b,c with b,c>=2a squared minus one, the actual ideal graph has an eigenvalue strictly between V-1 and V. The a=1 case is included: the general product inequality reduces to bc>0 for all positive tails. For a>=2, the natural truncated-subtraction bound transports exactly to the real uniform-tail inequality. These are applications of the general product theorem on all nonzero proper ideals. Failed sufficient criteria are not necessary-and-sufficient integrality tests.")),
            Item("four", "four_criterion", "The exact four-prime inequality", "The general product condition is algebraically equivalent to bc >= (a squared minus one)(b+c)+(a-1)(2a-1), over all real parameters."),
            Item("uniform", "uniform_tail", "The full uniform tail", "For every real a>=2 and b,c>=2a squared minus one, the four-prime criterion holds strictly, including both parameter boundaries."),
            Item("equality", "equality_family", "The entire equality family", "For every real a>=2, b=a squared and c=a to the fourth plus a squared minus 3a plus one are positive and satisfy the exact equality. This is an unbounded identity, not a fixed control."),
            Item("old-failure", "old_criterion_fails", "Every coordinate fails the earlier criterion", "For every real a>=2 the complete vector (a,a,2a squared minus one,2a squared minus one) fails all four choices of the earlier distinguished-coordinate sufficient criterion. The two source shifted-polynomial positivity identities prove the whole family. Failure of this earlier method asserts no integrality or priority.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum"))]));
}
