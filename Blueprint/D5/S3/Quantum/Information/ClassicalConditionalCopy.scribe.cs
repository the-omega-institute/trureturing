using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ClassicalConditionalCopyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ClassicalConditionalCopy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A physical conditional copy over a finite classical pointer, with unrestricted BC blocks.",
        H("Classical Pointer Conditional Copy"),
        Blocks(
            Paragraph(Text("Let X, B, C be finite carriers, p a nonnegative distribution of "
                + "total mass one on X, and tau_x an arbitrary density state on B tensor C. "
                + "The original state is recordState p tau. The copied state is the same "
                + "orthogonal pointer record with fragment tau_x tensor Tr_B(tau_x). "
                + "No orthogonality, commutativity or separability of the tau_x is assumed. "
                + "The pointer supplies orthogonality of the whole record components. "
                + "Weights may vanish, and singular and entangled BC blocks remain allowed.")),
            Result("discard", "conditionalCopy_discard", "Discarding E recovers the original state",
                "An actual finite-coordinate partial trace over the appended C carrier returns "
                    + "each tau_x, hence the original XBC density matrix.",
                Disp(Seq(Call("TrE", F.Id("omega")), Sp, Eq, Sp, Rho))),
            Result("copy-pointer", "conditionalCopy_pointer_copy", "The pointer-copy density agrees",
                "Tracing BC after an explicit index permutation gives recordState p "
                    + "(Tr_B tau). This is exactly the original XC density with E replacing C.",
                Disp(Seq(Call("omegaXE", F.Id("omega")), Sp, Eq, Sp,
                    Call("rhoXC", Rho)))),
            Result("total-entropy", "entropy_conditionalCopy", "The exact copy entropy",
                "The existing orthogonal-mixture entropy theorem applies to whole pointer "
                    + "components. Existing product-state entropy adds inside each block. "
                    + "Their finite weighted sums give the displayed equality in nats.",
                Disp(Seq(Call("S", F.Id("XBCE")), Sp, Eq, Sp,
                    Call("S", F.Id("XBC")), Sp, Plus, Sp, Call("S", F.Id("XE")),
                    Sp, Minus, Sp, Call("H", F.Id("p"))))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string text, Formula formula) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
