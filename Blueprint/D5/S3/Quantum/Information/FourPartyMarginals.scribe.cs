using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class FourPartyMarginalsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FourPartyMarginals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Zhang-Yeung defect is evaluated on actual four-party marginals.", H("Four Party Density Entropies"),
        Blocks(
            Paragraph(Text("A, B, C, D are arbitrary finite carriers. Each displayed entropy is the project natural-log entropy of a reduceState marginal, with its tensor-coordinate permutation defined explicitly. The defect is I(A:B)+I(A:CD)+3 I(C:D|A)+I(C:D|B)-2 I(C:D). Defining it makes no assertion of nonnegativity for unrestricted quantum states.")),
            Result("defect", "zhangYeungDefect", "The entropy defect", "Mutual and conditional mutual informations are expanded using the actual A, B, C, D, AB, AC, AD, BC, BD, CD, ACD and BCD density marginals. The final theorem restricts the input state to the AD-classical family.",
                Disp(Seq(Call("Delta", Rho), Sp, Eq, Sp, Call("ZY", Rho)))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
