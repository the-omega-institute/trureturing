using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class RepeatedPairModularResiduesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairModularResidues." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary parity and odd-prime discriminants", H("Binary parity and odd-prime discriminants"),
        Blocks(
            Paragraph(Text("Source: repeated-pair-modular, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blob 68f394977f82d9f5f20003d20797bb5706a72bff, with the actual product-tail graph lift. The full original scientific domains, attribution, source reports and failed-method/open boundaries remain binding. Exact source controls are historical reported evidence, not a claim that they were newly reproduced by Lean. General Q3 and cases passing all prime-divisor tests remain open. Academic approval/publication boundaries are unchanged. The escape audit remains unfinished under linked issue #28398.")),
            Item("quadratic-splits-iff-square", "quadratic_splits_iff_square", "Odd-characteristic square criterion including zero", "The completing-square equivalence requires exactly that two is nonzero."),
            Item("actual-binary-tails", "actual_binary_tails", "Every tail must be even for odd repeated exponent", "Every finite tail coordinate is tested on the actual ideal graph."),
            Item("actual-odd-pair-obstruction", "actual_odd_pair_obstruction", "An odd repeated exponent and any odd tail exclude integrality", "There is no bound on the other exponents or number of tails."),
            Item("actual-prime-discriminant", "actual_prime_discriminant", "Every odd prime divisor imposes a square-or-zero discriminant", "All prime divisors of a+1 and all tails are retained.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairModular"))]));
}
