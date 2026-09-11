using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ParityCode;

internal sealed class OddTopWeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/thompson2026a398720");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd square binary matrices of top even row and column weight are counted by factorial.",
        H("The odd-order boundary of A398720"),
        Blocks(Describe.Lean(
            DescribeId.Create("spcp-odd-top-weight"),
            DeclarationHandle.Create("D5/S1/Words/ParityCode/OddTopWeight.spcp_odd_top_weight"),
            H("The factorial count"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Call("Odd", F.Id("n")), Sp, Implies, Sp,
                Call("card", Call("Top", F.Id("n"))), Eq, F.Id("n"), Bang))),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Top(n) is the set of functions from Fin(n) to Fin(n) to Bool whose "
                    + "every row and every column has an even number of true entries and "
                    + "whose total number of true entries is n times (n minus one). "
                    + "Both indices use the n by n matrix convention in the OEIS comment "
                    + "and data. The entry explicitly conjectures this factorial count.")),
                Paragraph(Text(
                    "A row of odd length and even weight contains at least one zero. "
                    + "Equality in the sum of the row bounds forces exactly one zero in "
                    + "each row; transposing proves the same statement for columns. "
                    + "The unique zero positions form a permutation. Conversely, setting "
                    + "precisely the permutation positions to false gives a matrix with "
                    + "n minus one true entries in every row and column. The constructions "
                    + "are inverse, and the standard count of permutations completes the proof.")),
                Paragraph(Text(
                    "The proof covers every odd natural n, including n equal to one, "
                    + "where the only matrix is the single false entry and has weight zero."))),
            DescribeRole.Theorem))));
}
