using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class ShortGapOccupancyBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two prime hits give a consecutive gap.",
        H("Two prime hits give a consecutive gap"),
        Blocks(Describe.Lean(
            DescribeId.Create("short-gap-occupancy-bridge"),
            DeclarationHandle.Create("D5/S3/PrimeGaps/ShortGapOccupancyBridge.two_prime_occupancy_yields_consecutive_gap"),
            H("Two prime hits give a consecutive gap"),
            StatementSource.FromAuthor(F.Disp(
                F.Seq(F.Forall, F.Sp, F.Id("H"), F.InMacro, F.Sp, Call("Finset", F.Id("Nat")), F.Comma, F.Sp, F.Id("B"), F.Comma, F.Id("n"), F.InMacro, F.Sp, F.Id("Nat"), F.Comma, F.Sp, F.Grp(F.Forall, F.Sp, F.Id("h"), F.InMacro, F.Sp, F.Id("H"), F.Comma, F.Id("h"), F.Le, F.Sp, F.Id("B")), F.Land, F.D(2), F.Le, F.Sp, Call("primeTranslateOccupancy", F.Id("H"), F.Id("n")), F.Rightarrow, Call("BoundedConsecutivePrimeGapAt", F.Id("B"), F.Id("n"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This is the inherited two-hit theorem from PR 5236. For every finite natural offset set H and natural B,n, the two hypotheses are the bound on every offset and at least two prime hits at n. The conclusion retains the same interval [n,n+B], consecutive primality, and the explicit gap bound."))),
            DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
