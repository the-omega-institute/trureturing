using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CoherentCopyCorrelationTaxDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CoherentCopyCorrelationTax.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coherent premeasurement retains the input entropy and divides system-record "
            + "mutual information into diagonal entropy and relative entropy of coherence.",
        H("Coherent Premeasurement and Correlation Tax"),
        Blocks(
            Paragraph(Text(
                "The copying isometry sends basis vector i to the joint basis vector (i,i). "
                    + "The joint state is V rho V*, including the input's off-diagonal entries. "
                    + "Both marginals are obtained by partial trace.")),
            Result("correlated-entry", "coherentCopyState_correlated_entry",
                "Coherence survives on the correlated subspace",
                "For every input density state and every pair of indices, the joint matrix "
                    + "entry at (i,i),(j,j) equals the input entry at i,j.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    Call("jointEntry", Rho, F.Id("i"), F.Id("j")), Sp, Eq, Sp,
                    Call("inputEntry", Rho, F.Id("i"), F.Id("j"))))),
            Result("system-marginal", "marginalRight_coherentCopyState",
                "The system marginal is the pinched input",
                "Tracing out the record leaves precisely the diagonal of the input.",
                MarginalFormula("marginalRight")),
            Result("record-marginal", "marginalLeft_coherentCopyState",
                "The record marginal has the Born weights",
                "Tracing out the system produces the same diagonal state: its ith diagonal "
                    + "entry is rho(i,i), and its off-diagonal entries vanish.",
                MarginalFormula("marginalLeft")),
            Result("entropy", "vonNeumannEntropy_coherentCopyState",
                "Coherent copying preserves entropy",
                "The copying map preserves multiplication, adjoints and trace. Functional "
                    + "calculus transports the logarithm through this map, including zero "
                    + "eigenvalues, so the entropy trace is unchanged.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp,
                    Call("vonNeumannEntropy", Call("coherentCopyState", Rho)), Sp, Eq, Sp,
                    Call("vonNeumannEntropy", Rho)))),
            Result("correlation-tax", "coherent_copy_correlation_tax",
                "Correlation equals record entropy plus coherence tax",
                "The two marginal entropies are the diagonal entropy, and the joint entropy "
                    + "is the original entropy. The pinching entropy identity supplies the "
                    + "remaining relative entropy term.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp,
                    Call("quantumMutualInformation", Call("coherentCopyState", Rho)), Sp, Eq, Sp,
                    Call("vonNeumannEntropy", Call("basisPinchingState", Rho)), Sp, Plus, Sp,
                    Call("quantumRelativeEntropy", Rho, Call("basisPinchingState", Rho))))))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Quantum/codex2026correlationtax")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);

    private static Formula MarginalFormula(string name) => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, Call(name, Call("coherentCopyState", Rho)), Sp, Eq, Sp,
        Call("basisPinchingState", Rho)));
}
