using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class DiagonalPhaseBlindnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Tomography/DiagonalPhaseBlindness."
            + "diagonal_prime_observables_cannot_recover_relative_phase";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal observable families cannot recover relative phase without a non-diagonal "
            + "interface.",
        H("Diagonal Phase Blindness"),
        Blocks(Describe.Lean(
            DescribeId.Create("diagonal-prime-observables-cannot-recover-relative-phase"),
            DeclarationHandle.Create(Declaration),
            H("Diagonal observables cannot recover relative phase"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The equal superposition density and its conjugate by the canonical phase "
                        + "flip are distinct. Every indexed family of diagonal matrices gives "
                        + "the same joint trace-expectation readout on this pair, regardless of "
                        + "the size of the index type.")),
                Paragraph(Text(
                    "The second public clause uses the same pair: any matrix whose expectation "
                        + "separates the two states cannot be diagonal. The canonical Pauli X "
                        + "matrix supplies such a non-diagonal interface explicitly.")),
                Paragraph(Text(
                    "The family readout, trace expectation, diagonal predicate, states, and "
                        + "interface are existing repository or pinned-library primitives; no "
                        + "parallel observation carrier is introduced."))),
            DescribeRole.Theorem))));

    private static Formula Born(Formula state, Formula observable) =>
        Call("bornProbability", state, observable);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula index = F.Id("i");
        Formula observable = F.Id("observable");
        Formula state = F.Id("rho");
        Formula interfaceMatrix = F.Id("A");
        Formula plusState = F.Id("equalSuperpositionDensity");
        Formula phaseFlip = F.Id("qubitZ");
        Formula xInterface = F.Id("qubitX");
        Formula minusState = Call("mul", Call("mul", phaseFlip, plusState), phaseFlip);
        Formula matrixType = F.Id("QubitMatrix");
        Formula familyReadout = Call("jointReadout",
            Call("fun", index, state, Born(state, Call("observable", index))));
        Formula diagonalFamily = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Call("IsDiag", Call("observable", index)));
        Formula familyClause = Seq(
            Forall, Sp, observable, Colon, Sp, indexType, Sp, To, Sp, matrixType, Comma, Sp,
            Open, diagonalFamily, Close, Sp, Rightarrow, RowBreak, Grp(),
            NotEqual(plusState, minusState), Sp, Land, Sp,
            Equal(Call("apply", familyReadout, plusState),
                Call("apply", familyReadout, minusState)));
        Formula necessityClause = Seq(
            Forall, Sp, interfaceMatrix, Colon, Sp, matrixType, Comma, Sp,
            NotEqual(Born(plusState, interfaceMatrix), Born(minusState, interfaceMatrix)),
            Sp, Rightarrow, Sp, Neg, Sp, Call("IsDiag", interfaceMatrix));
        Formula witnessClause = Seq(
            Neg, Sp, Call("IsDiag", xInterface), Sp, Land, Sp,
            NotEqual(Born(plusState, xInterface), Born(minusState, xInterface)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, indexType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma),
            Seq(Open, familyClause, Close),
            Seq(Land, Sp, Open, necessityClause, Close),
            Seq(Land, Sp, Open, witnessClause, Close, Dot),
        ]));
    }
}
