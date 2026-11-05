using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FivePartySSA;

internal sealed class FivePartySSAConsistencyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FivePartySSA/Consistency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual four-party and five-party submarginals agree.", H("Marginal Consistency after Discarding E"),
        Blocks(
            Paragraph(Text("The composed coordinate sums show that first discarding E and then retaining any register set needed by the proof gives the same density, up to a basis permutation. Entropy is invariant under that permutation. These are consumed consistency lemmas, not extra hypotheses.")),
            Result("ad", "entropyAD_discard", "The AD entropy is unchanged", "The retained AD marginal has the same entropy whether taken directly or through the ABCD partial trace. All required sibling identities use the same actual trace composition theorem.",
                Disp(Seq(Call("SAD", Call("TrE", Rho)), Sp, Eq, Sp, Call("SAD", Rho)))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
