using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ProjectionProbabilityFlowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional Hamiltonian evolution differentiates projection probabilities "
            + "by the commutator trace and conserves them for commuting projections.",
        H("Projection Probability Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hamiltonian-projection-probability-flow"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow."
                        + "projection_probability_flow"),
                H("Projection probabilities follow the commutator trace"),
                StatementSource.FromAuthor(FlowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a positive trace-one state on a finite complex matrix "
                            + "algebra, let H be Hermitian, and let P be a star projection. "
                            + "The propagator is the matrix exponential of -i t H, the evolved "
                            + "state is U_t rho U_t^*, and p_P is the real Born probability.")),
                    Paragraph(Text(
                        "The first displayed conjunct identifies the complex cast of that real "
                            + "probability with the source Born trace. The next two conjuncts give "
                            + "its real derivative and certify that the complex commutator-trace "
                            + "flow is real, so the derivative equals the source formula exactly.")),
                    Paragraph(Text(
                        "The final conjunct is independent of the derivative clauses: if the "
                            + "Hamiltonian and projection commute, the probability is constant "
                            + "for every real time."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Trace(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Tr")), Open, value, Close);

    private static Formula Commutator(Formula left, Formula right) =>
        Seq(OpenBracket, left, Comma, right, CloseBracket);

    private static Formula FlowFormula()
    {
        Formula n = F.Id("n"), hamiltonian = F.Id("H"), projection = F.Id("P");
        Formula time = F.Id("t"), unitary = Sub(F.Id("U"), time);
        Formula state = Rho, evolved = Sub(Rho, time), probability = Sub(F.Id("p"), projection);
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrices = Seq(Sub(F.Id("M"), n), Open, complex, Close);
        Formula probabilityAtTime = At(probability, time);
        Formula traceAtTime = Trace(Seq(evolved, projection));
        Formula commutatorFlow = Seq(
            F.Id("i"), Sp, Trace(Seq(evolved, Commutator(hamiltonian, projection))));
        Formula realFlow = Seq(Re, Sp, commutatorFlow);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Comma, Sp, hamiltonian, Comma, Sp, projection, Comma, Sp, state,
            Comma, RowBreak, Grp(),
            Call("Finite", n), Comma, Sp,
            hamiltonian, Comma, Sp, projection, Sp, InMacro, Sp, matrices, Comma, Sp,
            Call("DensityState", state, n), Comma, Sp,
            Call("Hermitian", hamiltonian), Comma, Sp,
            Call("StarProjection", projection), Comma, RowBreak, Grp(),
            unitary, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("exp")), Open,
            Minus, Sp, F.Id("i"), Sp, time, Sp, hamiltonian, Close, Comma, Sp,
            evolved, Sp, Eq, Sp,
            unitary, Sp, state, Sp, unitary, Caret, Star, Comma, Sp,
            probabilityAtTime, Sp, Eq, Sp, Re, Sp, traceAtTime, Sp, InMacro, Sp, real,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, time, Sp, InMacro, Sp, real, Comma, Sp,
            Call("ofReal", probabilityAtTime), Sp, Eq, Sp, traceAtTime, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, time, Sp, InMacro, Sp, real, Comma, Sp,
            Frac, Grp(F.Id("d")), Grp(F.Id("d"), time), Sp,
            probabilityAtTime, Sp, Eq, Sp, realFlow, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, time, Sp, InMacro, Sp, real, Comma, Sp,
            Call("ofReal", realFlow), Sp, Eq, Sp, commutatorFlow, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Commutator(hamiltonian, projection), Sp, Eq, Sp, D(0), Sp,
            Rightarrow, Sp, Forall, Sp, time, Sp, InMacro, Sp, real, Comma, Sp,
            probabilityAtTime, Sp, Eq, Sp, At(probability, D(0)), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
