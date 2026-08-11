using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class RecordCorrelationMonogamyDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/ObserverMemory/RecordCorrelationMonogamy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/ObserverMemory/RecordCorrelationMonogamy",
            "A perfect Z-address copy in one fixed record pointer eliminates its conjugate X correlation."),
        H("Address-Record Correlation Monogamy"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-perfect-address-copy-eliminates-conjugate-correlation"),
                H("A perfect address copy eliminates conjugate correlation"),
                LeanTheorem(LeanPrefix + "record_correlation_monogamy"),
                MonogamyFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be an arbitrary positive semidefinite trace-one matrix on a "
                        + "system qubit and a two-address record. No diagonal, separable, or "
                        + "classical-mixture hypothesis is imposed. The record observable remains "
                        + "its fixed address pointer Z_R. For a system observable A, define "
                        + "C_A(rho) as the real part of Tr(rho(A tensor Z_R)). Thus C_Z tests an "
                        + "address copy and C_X tests the conjugate system observable against the "
                        + "same physical pointer.")),
                    Paragraph(Text(
                        "If C_Z(rho)=1, trace normalization and positivity force both mismatched "
                        + "address populations to vanish. For a positive semidefinite matrix, zero "
                        + "weight on a basis vector forces its entire row and column to vanish. "
                        + "Every nonzero matrix entry of X tensor Z_R joins an agreeing address "
                        + "basis vector to a mismatched one, so all four terms in C_X vanish. This "
                        + "is the structural no-cloning step carried by the theorem.")),
                    Paragraph(Text(
                        "The fixed-pointer clause is essential. Defining the second quantity as "
                        + "Tr(rho(X tensor X)) would make the proposed implication false: a Bell "
                        + "state has both Z-tensor-Z and X-tensor-X correlation equal to one. The "
                        + "theorem makes no diagonal-state restriction and no false Bell-state "
                        + "claim; it states what one classical address pointer can record.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-nondiagonal-state-has-nonzero-conjugate-correlation"),
                H("A non-diagonal state has nonzero conjugate correlation"),
                LeanTheorem(LeanPrefix + "coherent_record_anti_vacuity_certificate"),
                AntiVacuityFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The product state rho_(+0)=|+0><+0| is positive semidefinite and trace one. "
                    + "Its (00,10) entry is 1/2, so it is explicitly non-diagonal. It has "
                    + "C_Z=0 and C_X=1 against the fixed record pointer. Therefore C_X is not "
                    + "identically zero on the theorem's general domain; the main implication "
                    + "uses the perfect-copy premise.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-noisy-address-record-has-three-quarter-correlation"),
                H("A noisy address record has three-quarter correlation"),
                LeanTheorem(LeanPrefix + "three_quarter_address_record_certificate"),
                WitnessFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The numerical witness assigns 7/16 to each agreeing address pair and 1/16 "
                    + "to each disagreeing pair. Its diagonal embedding is a positive trace-one "
                    + "state with C_Z=3/4 and C_X=0. This explicit leg remains separate from the "
                    + "general-state theorem and supplies the requested nontrivial numerical "
                    + "reading.")))
            ))));

    private static Formula Correlation(Formula axis, Formula state) => Seq(
        F.Id("C"), Underscore, Grp(axis), Open, state, Close);

    private static Formula MonogamyFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Esc,
        Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("Tr")), Open, Rho, Close, Eq, D(1),
        Sp, Land, Sp,
        Correlation(F.Id("Z"), Rho), Eq, D(1),
        Sp, Rightarrow, RowBreak,
        Correlation(F.Id("X"), Rho), Eq, D(0), Dot));

    private static Formula AntiVacuityFormula()
    {
        Formula coherentState = Seq(Rho, Underscore, Grp(Plus, D(0)));
        return Disp(Seq(
            Operatorname, Grp(F.Id("PosSemidef")), Open, coherentState, Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Tr")), Open, coherentState, Close, Eq, D(1),
            Sp, Land, RowBreak,
            coherentState, Open, D(0), D(0), Comma, D(1), D(0), Close,
            Eq, Frac, Grp(D(1)), Grp(D(2)),
            Sp, Land, Sp,
            Correlation(F.Id("Z"), coherentState), Eq, D(0),
            Sp, Land, Sp,
            Correlation(F.Id("X"), coherentState), Eq, D(1), Dot));
    }

    private static Formula WitnessFormula()
    {
        Formula witnessState = Seq(Rho, Underscore, Grp(Frac, Grp(D(3)), Grp(D(4))));
        return Disp(Seq(
            Operatorname, Grp(F.Id("PosSemidef")), Open, witnessState, Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Tr")), Open, witnessState, Close, Eq, D(1),
            Sp, Land, RowBreak,
            Correlation(F.Id("Z"), witnessState), Eq, Frac, Grp(D(3)), Grp(D(4)),
            Sp, Land, Sp,
            Correlation(F.Id("X"), witnessState), Eq, D(0), Dot));
    }
}
