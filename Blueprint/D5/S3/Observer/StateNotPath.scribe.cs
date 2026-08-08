using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class StateNotPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Observer/StateNotPath",
            "Classical diagonal iteration and a one-step Hadamard witness separate coherence reachability."),
        H("Classical and Quantum Coherence Reachability"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("classical-diagonal-iterations-preserve-zero-coherence"),
                H("Classical diagonal iterations preserve zero coherence"),
                LeanTheorem(
                    "D5/S3/Observer/StateNotPath.classical_diagonal_iterates_off_diag_eq_zero"),
                ClassicalIterationFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For a qubit matrix rho, offDiag(rho) is the ordered pair of entries " +
                        "rho(0,1) and rho(1,0). The classical diagonal channel at a real " +
                        "retention coefficient c in [0,1] is the existing phase-damping map: " +
                        "it preserves diagonal entries and scales each off-diagonal entry by c.")),
                    Paragraph(Text(
                        "If offDiag(rho) is zero, induction over the standard finite function " +
                        "iterate shows that every later off-diagonal pair is zero. The statement " +
                        "quantifies over every coefficient, every finite iteration count, and " +
                        "every diagonal initial qubit matrix; no positivity or normalization " +
                        "premise is needed.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("one-hadamard-step-creates-exact-coherence"),
                H("One Hadamard step creates exact coherence"),
                LeanTheorem(
                    "D5/S3/Observer/StateNotPath.hadamard_basis_zero_off_diag_certificate"),
                HadamardWitnessFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The computational basis density matrix has entries 1, 0, 0, 0 and " +
                        "therefore starts with zero coherence. Applying the existing normalized " +
                        "Hadamard coordinate conjugation once gives both off-diagonal entries " +
                        "exactly one half. Hence its offDiag pair is (1/2, 1/2), which is " +
                        "algebraically nonzero.")),
                    Paragraph(Text(
                        "Together, the universal classical preservation theorem and this explicit " +
                        "one-step witness distinguish the two reachability mechanisms. The result " +
                        "is solely a finite two-by-two matrix certificate and introduces no new " +
                        "probability law or measurement premise.")))
            ))));

    private static Formula ClassicalIterationFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("c"), Sp, InMacro, Sp,
        OpenBracket, D(0), Comma, Sp, D(1), CloseBracket, Comma, RowBreak,
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak,
        Forall, Sp, Rho, Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("QubitMatrix")), Comma, RowBreak,
        Operatorname, Grp(F.Id("offDiag")), Open, Rho, Close, Eq, D(0),
        Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("offDiag")), Open,
        Open,
        Operatorname, Grp(F.Id("classicalDiagonalChannel")),
        Open, F.Id("c"), Close,
        Close, Caret, Grp(F.Id("n")),
        Open, Rho, Close,
        Close, Eq, D(0), Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula HadamardWitnessFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Operatorname, Grp(F.Id("offDiag")), Open,
        Operatorname, Grp(F.Id("hadamardCoordinates")), Open,
        Operatorname, Grp(F.Id("basisZeroDensity")), Close,
        Close,
        Eq,
        Open, Frac, Grp(D(1)), Grp(D(2)), Comma, Sp,
        Frac, Grp(D(1)), Grp(D(2)), Close,
        Sp, Land, Sp, RowBreak,
        Operatorname, Grp(F.Id("offDiag")), Open,
        Operatorname, Grp(F.Id("hadamardCoordinates")), Open,
        Operatorname, Grp(F.Id("basisZeroDensity")), Close,
        Close,
        Neq, Sp, D(0), Dot,
        End, Grp(F.Id("gathered"))));
}
