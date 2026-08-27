using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ComputationalBasisKernelPreservationDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Quantum/Measurements/ComputationalBasisKernelPreservation."
            + "computational_basis_kernel_preservation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Basis fiber projectors preserve the deterministic readout kernel.",
        H("Computational-Basis Kernel Preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("computational-basis-kernel-preservation"),
                DeclarationHandle.Create(Gid),
                H("Fiber projectors retain exactly the deterministic kernel"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite state type and O an outcome type with decidable "
                            + "equality. The density matrix rho of a state is the canonical "
                            + "coordinate rank-one projector.")),
                    Paragraph(Text(
                        "For each outcome, its projector is constructed as the finite sum of "
                            + "coordinate projectors over the corresponding q-fiber. The trace "
                            + "pairing with rho is therefore the fiber indicator.")),
                    Paragraph(Text(
                        "Equality of every outcome probability follows from equal q-values. "
                            + "Conversely, evaluating the common signature at q(x) forces the "
                            + "two q-values to agree."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula outcomeType = F.Id("O");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula matrix = Call("Matrix", stateType, stateType, complex);
        Formula readout = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula state = F.Id("z");
        Formula outcome = F.Id("o");
        Formula density = Rho;
        Formula projector = F.Id("P");
        Formula densityAt(Formula value) => Apply(density, value);
        Formula projectorAt(Formula value) => Apply(projector, value);
        Formula readoutAt(Formula value) => Apply(readout, value);
        Formula traceProbability(Formula value, Formula result) =>
            Call("Tr", Call("mul", densityAt(value), projectorAt(result)));
        Formula fiberSum = Seq(
            Sum, Underscore, Grp(
                state, Sp, InMacro, Sp, stateType, Comma, Sp,
                readoutAt(state), Sp, Eq, Sp, outcome), Sp,
            Call("basisProjector", state));
        Formula densityDefinition = Seq(
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            densityAt(state), Sp, Eq, Sp, Call("basisProjector", state));
        Formula projectorDefinition = Seq(
            Forall, Sp, Typed(outcome, outcomeType), Comma, Sp,
            projectorAt(outcome), Sp, Eq, Sp, fiberSum);
        Formula bornClause = Seq(
            Forall, Sp, Typed(outcome, outcomeType), Comma, Sp,
            traceProbability(left, outcome), Sp, Eq, Sp,
            Call("indicator", Seq(readoutAt(left), Sp, Eq, Sp, outcome)));
        Formula kernelClause = Seq(
            readoutAt(left), Sp, Eq, Sp, readoutAt(right), Sp, Iff, Sp,
            Forall, Sp, Typed(outcome, outcomeType), Comma, Sp,
            traceProbability(left, outcome), Sp, Eq, Sp,
            traceProbability(right, outcome));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(stateType, type), Comma, Sp,
            Typed(outcomeType, type), Comma, RowBreak, Grp(),
            OpenBracket, Call("Fintype", stateType), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", stateType), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", outcomeType), CloseBracket, Comma,
            RowBreak, Grp(),
            Typed(readout, Arrow(stateType, outcomeType)), Comma, Sp,
            Typed(left, stateType), Comma, Sp, Typed(right, stateType), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            Typed(density, Arrow(stateType, matrix)), Comma, Sp,
            densityDefinition, Comma, RowBreak, Grp(),
            Typed(projector, Arrow(outcomeType, matrix)), Comma, Sp,
            projectorDefinition, Close, SemiSpace,
            OpenBracket, bornClause, CloseBracket, Sp, Land, RowBreak, Grp(),
            OpenBracket, kernelClause, CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
