using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GreedyBrick;

internal sealed class RestBlockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal capacity steps realize the least-zero rest block.",
        H("Literal Capacity Steps and First-Zero Rest Blocks"),
        Blocks(Describe.Lean(
            DescribeId.Create("literal-rest-block"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/GreedyBrick/RestBlock.literal_rest_block"),
            H("The relay reaches exactly the first zero bin"),
            StatementSource.FromAuthor(LiteralRestBlockFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A rest state consists of an endpoint N and a finite capacity list "
                    + "whose entries are at most N. Rest capacities are indexed from bottom "
                    + "to top. The single-brick capacity algorithm scans from top "
                    + "to bottom, so the realization reverses the list at both boundaries. "
                    + "Let k be the one-based first zero bin, or height plus one when no "
                    + "old bin is zero. Applying the actual step at widths N+1 through N+k "
                    + "produces a bounded target satisfying every RestEventStep clause.")),
                Paragraph(Text(
                    "The endpoint is N+k and the target height is max(height,k). "
                    + "Every bin below k was positive and decreases by exactly one; "
                    + "bin k resets to N+k; every higher bin is unchanged. When all old "
                    + "bins are positive exactly one new top bin is appended. Empty states "
                    + "and k=1 remain in the theorem's domain.")),
                Paragraph(Text(
                    "The initial bound forces the first placement onto the floor. "
                    + "At a subsequent relay the current recipient has capacity N+a. "
                    + "If a is positive, the next width N+1 is eligible there and leaves "
                    + "a-1 while transferring upward. All higher capacities are below "
                    + "that width. The first zero stops the ascent. Induction uses the "
                    + "transfer and step definitions, rather than assuming the "
                    + "rest-event recurrence.")),
                Paragraph(Text(
                    "This theorem closes the capacity-step to rest-block bridge. "
                    + "It does not identify capacity states with geometric placements, "
                    + "construct a chronological event history, prove reset balance or "
                    + "future same-bin successors, or prove the original OEIS A395531 "
                    + "self-composition identity."))),
            DescribeRole.Theorem)),
        []));

    private static Formula LiteralRestBlockFormula()
    {
        var s = F.Id("s");
        var t = F.Id("t");
        var firstZero = Call("firstZeroBin", Call("capacity", s));
        var transition = Call("RestEventStep", s, t, firstZero);
        var placement = Call(
            "placeBricks",
            Call("endpoint", s),
            Call("reverse", Call("capacity", s)),
            firstZero);
        var targetCapacity = Call("reverse", Call("capacity", t));
        return Disp(Seq(
            Forall, Sp, s, Sp, Colon, Sp, F.Id("RestState"), Comma, Sp,
            Exists, Sp, t, Sp, Colon, Sp, F.Id("RestState"), Comma, Sp,
            transition, Sp, Land, Sp, placement, Sp, Eq, Sp, targetCapacity));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
