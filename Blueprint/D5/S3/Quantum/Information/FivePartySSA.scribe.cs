using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class FivePartySSADocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FivePartySSA.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantum five-party precursor is the sum of eleven actual nonnegative CMIs.", H("Eleven Actual Strong Subadditivities"),
        Blocks(
            Paragraph(Text("Apply actual density SSA to I(A:B|E), I(A:D|CE), I(A:E|BCD), I(B:E|C), I(B:E|D), I(B:E|ACD), I(C:D|BE), I(C:E|A), I(C:E|AB), I(C:E|D), and I(D:E|ABC). Each term is evaluated on a genuine partial trace and index permutation of the same five-party state. Finite exact linear arithmetic combines these eleven inequalities.")),
            Result("eleven", "eleven_cmi_nonnegative", "The eleven-term precursor", "The sum is -S(A)-S(C)-2S(D)-S(E)-S(AB)+S(AC)+2S(AE)+S(BC)+S(BD)+S(CD)+2S(DE)-S(ACD)-S(BCD)+3S(ABCD)-3S(ABCDE). This precursor holds for arbitrary quantum five-party states; the copy construction is used only in the final AD theorem.",
                Disp(Seq(D(0), Sp, Le, Sp, Call("ElevenCMIs", Rho)))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
