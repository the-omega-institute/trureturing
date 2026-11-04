using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ClassicalADCopyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ClassicalADCopy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The copied density is built from arbitrary conditional BC states over a classical AD pointer.", H("Physical AD Conditional Copy"),
        Blocks(
            Paragraph(Text("Let p_ad be any finite nonnegative distribution of total mass one, and tau_ad any DensityState on B tensor C. classicalADState reorders recordState p tau into ABCD. copyState reorders recordState p (tau tensor Tr_B tau) into ABCDE, with E using C's finite carrier. Zero-weight blocks remain arbitrary. Conditional entanglement, singular states, and noncommuting C marginals are allowed.")),
            Result("discard", "copyState_discard", "The physical copy recovers the original state", "The actual E partial trace of the ABCDE copy is exactly classicalADState p tau as a density state, not merely an entropy equality.",
                Disp(Seq(Call("TrE", F.Id("omega")), Sp, Eq, Sp, Rho))),
            Result("ade", "copy_ade_eq_relabel", "ADE matches ACD as an actual density", "An explicit coordinate equivalence sends the original ACD marginal to the copied ADE marginal. In particular S(E)=S(C), S(AE)=S(AC), S(DE)=S(CD), and S(ADE)=S(ACD); the smaller equalities are also proved from actual traces.",
                Disp(Seq(Call("omegaADE", F.Id("omega")), Sp, Eq, Sp, Call("relabel", Call("rhoACD", Rho))))),
            Result("total", "copy_entropy_total", "The total copy entropy", "Orthogonal CQ record entropy and product entropy imply S(ABCDE)=S(ABCD)+S(ACD)-S(AD), without any assumption on those entropy values.",
                Disp(Seq(Call("S", F.Id("ABCDE")), Sp, Eq, Sp, Call("S", F.Id("ABCD")), Sp, Plus, Sp, Call("S", F.Id("ACD")), Sp, Minus, Sp, Call("S", F.Id("AD"))))),
            Result("zero-cmi", "copy_zero_cmi", "The actual conditional copy is Markov over AD", "The constructed state satisfies I(E:BC|AD)=0. This exact equality is consumed by the final theorem together with the eleven-SSA precursor.",
                Disp(Seq(Call("CMI", F.Id("E"), F.Id("BC"), F.Id("AD")), Sp, Eq, Sp, D(0)))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
