using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sumfree;

internal sealed class StrictTwoSumfreePreperiodRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/vanberkelbosma2026periodicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict greedy sequence with seeds 5 and 21 has no positive gap period after nine gaps.",
        H("The printed preperiod formula for the strict greedy sequence with seeds 5 and 21"),
        Blocks(
            Describe.Lean(DescribeId.Create("printed-preperiod"), DeclarationHandle.Create(Prefix + "claim"),
                H("The specialized assertion"), StatementSource.FromAuthor(Disp(Call("HasGapPreperiod",
                    Call("S", D(5), D(2, 1)), D(9)))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "S(5,21) starts with 5 and 21. Each later entry is the least larger natural "
                    + "number avoiding sums of two distinct earlier entries. HasGapPreperiod(S,k) "
                    + "says that k is the least number of initial differences to discard for the "
                    + "remaining differences to have a positive period. "
                    + "At d=16=6+1*10, Definition 8(e) gives 30 and (k1) subtracts 21. "
                    + "Conjecture 9 applied to these seeds therefore asserts preperiod length 9. "
                    + "Example 10 lists 15 for the same pair."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gap-refutation"), DeclarationHandle.Create(Prefix + "result"),
                H("No positive gap period starts after nine gaps"),
                StatementSource.FromAuthor(Disp(new Formula.Not(FormulaDsl.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The explicit increasing enumeration has a finite head and translates "
                    + "of a fourteen-entry block by multiples of 56. The greedy recurrence "
                    + "is certified through 288 and by strict-sum residue arguments from 288 onward. "
                    + "The least-next-entry rule gives uniqueness. At zero-based gap index 14, "
                    + "the difference from 51 to 61 is 10. Every later difference is at most 9, "
                    + "so any positive shift of gap 14 violates the proposed periodicity."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("van-berkel-bosma-2026-conjecture-9"),
                    ResolutionKind.Refuted)))));

}
