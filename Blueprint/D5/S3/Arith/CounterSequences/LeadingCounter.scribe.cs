using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CounterSequences;

internal sealed class LeadingCounterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CounterSequences/LeadingCounter.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/sycamore2025a384309");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive integer occurs nine times in A384309, except 1 which occurs ten times.",
        H("Exact multiplicities in the leading-digit counter sequence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leading-counter-initial"),
                DeclarationHandle.Create(Prefix + "a_one"),
                H("Initial term"),
                StatementSource.FromAuthor(Disp(Seq(Call("a", D(1)), Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The sequence starts at position 1. The auxiliary value at position 0 is "
                    + "zero, so it contributes no occurrence of a positive integer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("leading-counter-recurrence"),
                DeclarationHandle.Create(Prefix + "a_recurrence"),
                H("Count the current term before reading the next term"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Here counter(d,t) counts positions j from 1 through t with leading10(a(j))=d. "
                    + "The leading digit is the last element of Mathlib's little-endian decimal "
                    + "digit list. At each step exactly one of the nine counters increases by one, "
                    + "and its new value becomes the next term."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("leading-counter-multiplicity"),
                DeclarationHandle.Create(Prefix + "leading_counter_multiplicity"),
                H("Nine occurrences, with one extra initial 1"),
                StatementSource.FromAuthor(MultiplicityFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "O(k) denotes the set of natural positions n for which a(n)=k; "
                        + "ncard is its cardinality, and the indicator is one exactly when k=1. "
                        + "Finiteness is part of the conclusion.")),
                    Paragraph(Text(
                        "Some digit class occurs infinitely often by the infinite pigeonhole "
                        + "principle. Its successive visits emit every positive integer. For "
                        + "each digit d, the numbers d times powers of ten are distinct and "
                        + "have leading digit d, so every digit class occurs infinitely often.")),
                    Paragraph(Text(
                        "Fix a positive k. Send each successor occurrence of k to the digit "
                        + "class of its predecessor. This is injective because a counter never "
                        + "repeats a value when incremented, and surjective because every counter "
                        + "has a k-th visit. Thus there are nine successor occurrences. The "
                        + "initial position contributes one more exactly for k=1."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Bound(string name) => Seq(
        Forall, Sp, F.Id(name), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp);
    private static Formula RecurrenceFormula() => Disp(Seq(
        Bound("t"), D(0), Sp, Lt, Sp, F.Id("t"), Sp, Implies, Sp,
        Call("a", Seq(F.Id("t"), Plus, D(1))), Sp, Eq, Sp,
        Call("counter", Call("leading10", Call("a", F.Id("t"))), F.Id("t"))));
    private static Formula MultiplicityFormula() => Disp(Seq(
        Bound("k"), D(0), Sp, Lt, Sp, F.Id("k"), Sp, Implies, Sp,
        Call("finite", Call("O", F.Id("k"))), Sp, Land, Sp,
        Call("ncard", Call("O", F.Id("k"))), Sp, Eq, Sp, D(9), Plus,
        Mathbf, Grp(D(1)), Underscore, Grp(F.Id("k"), Eq, D(1))));
}
