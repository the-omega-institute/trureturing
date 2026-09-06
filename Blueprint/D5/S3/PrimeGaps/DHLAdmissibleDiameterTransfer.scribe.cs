using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class DHLAdmissibleDiameterTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent occupancy and window inputs.",
        H("Independent occupancy and window inputs"),
        Blocks(Describe.Lean(
            DescribeId.Create("d-h-l-admissible-diameter-transfer"),
            DeclarationHandle.Create("D5/S3/PrimeGaps/DHLAdmissibleDiameterTransfer.dhl_two_and_admissible_window_yield_bounded_gap"),
            H("Independent occupancy and window inputs"),
            StatementSource.FromAuthor(F.Disp(
                F.Seq(F.Forall, F.Sp, F.Id("k"), F.Comma, F.Id("B"), F.InMacro, F.Sp, F.Id("Nat"), F.Comma, Call("DHLTwoNat", F.Id("k")), F.Land, Call("AdmissibleWindowWitness", F.Id("k"), F.Id("B")), F.Rightarrow, Call("ArbitrarilyLateConsecutiveGap", F.Id("B"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This inherited API theorem combines the exact DHLTwoNat k premise with the existence of a k-element admissible natural set whose offsets are bounded by B. It asserts arbitrarily late consecutive prime gaps in a containing window of width B; it does not prove the analytic premise."))),
            DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
