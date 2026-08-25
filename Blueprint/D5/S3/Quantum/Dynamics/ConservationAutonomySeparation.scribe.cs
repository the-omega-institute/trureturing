using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ConservationAutonomySeparationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/ConservationAutonomySeparation."
            + "conservation_and_autonomy_are_distinct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conservation of one observable is distinct from autonomy of an observable space.",
        H("Conservation And Autonomy Are Distinct"),
        Blocks(Describe.Lean(
            DescribeId.Create("conservation-and-autonomy-are-distinct"),
            DeclarationHandle.Create(Declaration),
            H("An autonomous observable space need not be stationary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For finite complex matrices, a zero Hamiltonian commutator makes the "
                        + "Heisenberg conjugation of the observable constant at every real "
                        + "time.")),
                Paragraph(Text(
                    "The explicit contrast uses the self-adjoint qubit Z and X matrices. "
                        + "The trace-zero observable space contains X and is preserved by "
                        + "commutation with Z, while the commutator of Z and X is nonzero."))),
            DescribeRole.Theorem))));

    private static Formula Commutator(Formula left, Formula right) =>
        Seq(OpenBracket, left, Comma, Sp, right, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("n");
        Formula hamiltonian = F.Id("H");
        Formula observable = F.Id("A");
        Formula time = F.Id("t");
        Formula qubitZ = F.Id("Z");
        Formula qubitX = F.Id("X");
        Formula matrixSpace = Call("Mat", index, F.Id("C"));
        Formula traceKernel = Call("ker", F.Id("tr"));

        Formula sourceCarrier = Seq(
            Call("finite", index), Comma, Sp,
            hamiltonian, Comma, Sp, observable, Sp, InMacro, Sp, matrixSpace,
            Comma, Sp,
            Call("star", hamiltonian), Sp, Eq, Sp, hamiltonian, Comma, Sp,
            Call("star", observable), Sp, Eq, Sp, observable);

        Formula conserved = Seq(
            Commutator(hamiltonian, observable), Sp, Eq, Sp, D(0), Sp,
            Rightarrow, Sp, Forall, Sp, time, InMacro, Sp, F.Id("R"), Comma, Sp,
            Call("U", hamiltonian, Seq(Minus, time)), Sp, observable, Sp,
            Call("U", hamiltonian, time), Sp, Eq, Sp, observable);

        Formula contrast = Seq(
            Call("star", qubitZ), Sp, Eq, Sp, qubitZ, Sp, Land, Sp,
            Call("star", qubitX), Sp, Eq, Sp, qubitX, Sp, Land, Sp,
            qubitX, Sp, InMacro, Sp, traceKernel, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, F.Id("B"), Sp, InMacro, Sp, traceKernel, Comma, Sp,
            Commutator(qubitZ, F.Id("B")), Sp, InMacro, Sp, traceKernel, Close,
            Sp, Land, Sp,
            Commutator(qubitZ, qubitX), Sp, Neq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, index, Comma, Sp, sourceCarrier, Comma,
            RowBreak, Grp(),
            Open, conserved, Close, Sp, Land, Sp,
            Open, contrast, Close, Dot));
    }
}
