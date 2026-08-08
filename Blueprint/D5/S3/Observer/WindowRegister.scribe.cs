using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class WindowRegisterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Observer/WindowRegister",
            "Finite cyclic clock and shift matrices obey Weyl, periodicity, unitarity, and scalar-commutant relations."),
        H("Finite Cyclic Window Register"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-window-phase-is-a-primitive-root"),
                H("The window phase is a primitive root"),
                LeanTheorem(
                    "D5/S3/Observer/WindowRegister.windowRoot_isPrimitiveRoot"),
                PrimitiveRootFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural window cardinality M, the standard phase " +
                        "omega_M = exp(2 pi i/M) is a primitive M-th root of unity. The positivity " +
                        "condition is the displayed form of the formal NeZero M instance; the " +
                        "declaration makes no claim for a zero-cardinality window.")),
                    Paragraph(Text(
                        "Provenance note: OBSERVER-QUANTUM.md section 3 motivates the finite-window " +
                        "interpretation. It is reference input only. The typed Lean declaration " +
                        "above is the source of this theorem, and Scribe generates its number.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-clock-and-shift-obey-the-finite-weyl-relation"),
                H("The clock and shift obey the finite Weyl relation"),
                LeanTheorem("D5/S3/Observer/WindowRegister.window_weyl"),
                WeylFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Write V_M for the diagonal clock with entries omega_M raised to the " +
                        "standard representatives of Z/MZ, and U_M for the circulant shift whose " +
                        "entry at (r,s) is one exactly when r - s = 1. With these conventions the " +
                        "formal matrix identity has the displayed orientation.")),
                    Paragraph(Text(
                        "The proof is entrywise. At the unique nonzero shift entry, additivity of " +
                        "the standard Z/MZ character advances the clock phase by omega_M; every " +
                        "other entry vanishes on both sides. The section-3 provenance is restricted " +
                        "here to this fixed finite matrix window: no crossed-product universal " +
                        "property or central winding relation is asserted.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-cyclic-shift-closes-at-the-window-cardinality"),
                H("The cyclic shift closes at the window cardinality"),
                LeanTheorem(
                    "D5/S3/Observer/WindowRegister.shiftMatrix_pow_card"),
                ShiftPowerFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The circulant shift U_M is the permutation matrix for translation by one " +
                        "on Z/MZ. Applying that permutation M times is the identity, so its M-th " +
                        "matrix power is I_M. This is only the fixed-window closure U_M^M = I_M; it " +
                        "does not introduce a central winding phase.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-clock-phases-close-at-the-window-cardinality"),
                H("The clock phases close at the window cardinality"),
                LeanTheorem(
                    "D5/S3/Observer/WindowRegister.clockMatrix_pow_card"),
                ClockPowerFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Each diagonal entry of V_M is a power of the primitive phase omega_M. " +
                        "Raising V_M to the M-th power therefore raises every entry to a multiple " +
                        "of M, giving the identity matrix I_M.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-finite-window-generators-are-unitary"),
                H("The finite-window generators are unitary"),
                LeanTheorem("D5/S3/Observer/WindowRegister.window_unitary"),
                UnitaryFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The shift U_M is a permutation matrix, so its conjugate transpose is its " +
                        "inverse. The clock V_M is diagonal and every diagonal phase has complex " +
                        "norm one. Consequently both displayed star-products are the identity.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-joint-commutant-consists-of-scalars"),
                H("The joint commutant consists of scalars"),
                LeanTheorem(
                    "D5/S3/Observer/WindowRegister.window_commutant_eq_scalars"),
                CommutantFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let A be an M-by-M complex matrix indexed by Z/MZ. Commutation with the " +
                        "clock V_M forces every off-diagonal entry of A to vanish because distinct " +
                        "indices carry distinct powers of the primitive phase. Commutation with the " +
                        "shift U_M then propagates equality around the diagonal. Thus A is lambda " +
                        "times I_M for a complex scalar lambda.")),
                    Paragraph(Text(
                        "This is the scalar joint-commutant statement for the two concrete finite " +
                        "generators. The section-3 provenance supplies the motivating observer " +
                        "language only; the theorem does not identify an abstract crossed product, " +
                        "a continuous field, or a holonomy class.")))
            ))));

    private static Formula PrimitiveRootFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
        Operatorname, Grp(F.Id("IsPrimitiveRoot")), Open,
        F.Id("e"), Caret, Grp(Frac, Grp(D(2), Pi, Sp, F.Id("i")), Grp(F.Id("M"))),
        Comma, Sp, F.Id("M"), Close));

    private static Formula WeylFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
        F.Id("V"), Underscore, Grp(F.Id("M")), F.Id("U"), Underscore,
        Grp(F.Id("M")), Sp, Eq, Sp, Omega, Underscore, Grp(F.Id("M")),
        Cdot, Sp, Open, F.Id("U"), Underscore, Grp(F.Id("M")), F.Id("V"),
        Underscore, Grp(F.Id("M")), Close));

    private static Formula ShiftPowerFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
        F.Id("U"), Underscore, Grp(F.Id("M")), Caret, Grp(F.Id("M")),
        Sp, Eq, Sp, F.Id("I"), Underscore, Grp(F.Id("M"))));

    private static Formula ClockPowerFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
        F.Id("V"), Underscore, Grp(F.Id("M")), Caret, Grp(F.Id("M")),
        Sp, Eq, Sp, F.Id("I"), Underscore, Grp(F.Id("M"))));

    private static Formula UnitaryFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
        F.Id("U"), Underscore, Grp(F.Id("M")), Caret, Grp(Star),
        F.Id("U"), Underscore, Grp(F.Id("M")), Sp, Eq, Sp,
        F.Id("I"), Underscore, Grp(F.Id("M")), Sp, Land, Sp,
        F.Id("V"), Underscore, Grp(F.Id("M")), Caret, Grp(Star),
        F.Id("V"), Underscore, Grp(F.Id("M")), Sp, Eq, Sp,
        F.Id("I"), Underscore, Grp(F.Id("M"))));

    private static Formula CommutantFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, RowBreak,
        Forall, Sp, F.Id("A"), Sp, InMacro, Sp,
        F.Id("M"), Underscore, Grp(F.Id("M")),
        Open, Mathbb, Grp(F.Id("C")), Close, Comma, RowBreak,
        Open,
        F.Id("A"), F.Id("V"), Underscore, Grp(F.Id("M")), Sp, Eq, Sp,
        F.Id("V"), Underscore, Grp(F.Id("M")), F.Id("A"), Sp, Land, Sp,
        F.Id("A"), F.Id("U"), Underscore, Grp(F.Id("M")), Sp, Eq, Sp,
        F.Id("U"), Underscore, Grp(F.Id("M")), F.Id("A"),
        Close, Sp, Rightarrow, RowBreak,
        Exists, Sp, LambdaLower, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")),
        Comma, Esc, F.Id("A"), Sp, Eq, Sp, LambdaLower, Cdot, Sp,
        F.Id("I"), Underscore, Grp(F.Id("M")), Dot,
        End, Grp(F.Id("gathered"))));
}
