using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FivePartySSA;

internal sealed class FivePartySSAMarginalsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FivePartySSA/Marginals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor permutations and partial traces define all marginals used by the copy proof.", H("Five Party Actual Marginals"),
        Blocks(
            Paragraph(Text("For a density on A tensor B tensor C tensor D tensor E, splitS puts the retained registers S first and their complement second. marginalS is reduceState splitS rho. Thus all entropy expressions belong to one actual density state; no abstract entropy-vector realization is assumed.")),
            Result("abcd", "marginalABCD", "Discard the copied register", "marginalABCD traces the E index from the actual five-party matrix. The definition is consumed by the physical copy-discard identity and the marginal consistency lemmas.",
                Disp(Seq(Call("marginalABCD", Rho), Sp, Eq, Sp, Call("TrE", Rho)))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
