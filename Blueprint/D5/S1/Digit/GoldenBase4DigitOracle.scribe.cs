using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4DigitOracleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact floor arithmetic supplies the base-four golden digit oracle and canonical power samples.",
        H("Golden Base-Four Digit Oracle"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-power-samples-decode-exactly"),
            DeclarationHandle.Create(
                "D5/S1/Digit/GoldenBase4DigitOracle.decode_powerOccupiedIndices"),
            H("Canonical power samples decode exactly"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("decode", Call("powerOccupiedIndices", F.Id("i"))),
                Sp, Eq, Sp, Call("pow", D(4), F.Id("i")), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The input sample reuses the canonical Zeckendorf occupied-index representation already supplied by WDigits.")),
                Paragraph(Text(
                    "The output oracle is the final radix-four remainder of the exact natural floor of 4^(i+1) times the golden ratio.")),
                Paragraph(Text(
                    "Bit-stream serialization and the published Walnut input convention remain explicit later obligations."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Conventions/WDigits")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
