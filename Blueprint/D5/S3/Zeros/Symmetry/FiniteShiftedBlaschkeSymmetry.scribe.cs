using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class FiniteShiftedBlaschkeSymmetryDocument : IScribeDocumentDefinition
{
    private static Formula Sigma(Formula value) =>
        Seq(F.Id("sigma"), Open, value, Close);

    private static Formula XiAt(Formula value) =>
        Seq(Xi, Open, value, Close);

    private static Formula MirrorSpec(Formula value) =>
        Seq(Operatorname, Grp(F.Id("MirrorSpec")), Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Open, value, Close);

    public DocumentDefinition Create()
    {
        var half = new Formula.Fraction(Num(1), Num(2));
        var sigmaRho = Sigma(Rho);
        var positiveWindow = Seq(
            D(0), Sp, Lt, Sp, ImaginaryPart(Rho),
            Sp, Land, Sp, ImaginaryPart(Rho), Sp, Leq, Sp, F.Id("T"));
        var reflectedWindow = Seq(
            D(0), Sp, Lt, Sp, ImaginaryPart(sigmaRho),
            Sp, Land, Sp, ImaginaryPart(sigmaRho), Sp, Leq, Sp, F.Id("T"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Conjugate reflection preserves positive zero windows and fixes exactly "
            + "the critical line.",
            H("Finite Shifted-Blaschke Symmetry"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("critical-line-mirror-specification"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry."
                        + "critical_line_mirror_spec"),
                    H("Conjugate reflection has the critical line as its fixed locus"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Sigma(Rho), Sp, Colon, Eq, Sp, D(1), Sp, Minus, Sp,
                        Overline, Grp(Rho), Comma, Esc,
                        Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
                        Sigma(sigmaRho), Sp, Eq, Sp, Rho, Sp, Land, Sp,
                        ImaginaryPart(sigmaRho), Sp, Eq, Sp, ImaginaryPart(Rho),
                        Sp, Land, Sp,
                        Open, Re, Open, sigmaRho, Close, Sp, Minus, Sp, half, Close,
                        Sp, Eq, Sp, Minus,
                        Open, Re, Open, Rho, Close, Sp, Minus, Sp, half, Close,
                        Sp, Land, Sp,
                        Open, sigmaRho, Sp, Eq, Sp, Rho,
                        Sp, Leftrightarrow, Sp,
                        Re, Open, Rho, Close, Sp, Eq, Sp, half, Close, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen reflection sigma sends rho to one minus its complex "
                        + "conjugate. It is involutive, preserves the imaginary coordinate, "
                        + "reverses signed displacement from real part one half, and fixes "
                        + "exactly the critical line."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("finite-shifted-blaschke-reflection-specification"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry."
                        + "finite_shifted_blaschke_reflection_spec"),
                    H("Abstract xi zeros remain in the positive ordinate window"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open,
                        Forall, Sp, F.Id("s"), Comma, Esc,
                        XiAt(Seq(D(1), Sp, Minus, Sp, F.Id("s"))),
                        Sp, Eq, Sp, XiAt(F.Id("s")), Close,
                        Sp, Land, Sp,
                        Open,
                        Forall, Sp, F.Id("s"), Comma, Esc,
                        XiAt(Seq(Overline, Grp(F.Id("s")))),
                        Sp, Eq, Sp, Overline, Grp(XiAt(F.Id("s"))), Close,
                        Sp, Rightarrow, Sp,
                        Forall, Sp, F.Id("T"), Comma, Esc,
                        D(0), Sp, Lt, Sp, F.Id("T"), Sp, Rightarrow, Sp,
                        Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
                        MirrorSpec(Rho), Sp, Land, Sp,
                        Open, XiAt(Rho), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
                        XiAt(sigmaRho), Sp, Eq, Sp, D(0), Close,
                        Sp, Land, Sp,
                        Open, positiveWindow, Sp, Rightarrow, Sp, reflectedWindow, Close,
                        Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For an abstract complex function xi, the functional equation and "
                            + "conjugation covariance are explicit hypotheses. Their composition "
                            + "proves that sigma transports a zero to a zero; zero stability is "
                            + "not introduced as a third hypothesis.")),
                        Paragraph(Text(
                            "MirrorSpec denotes the four laws proved immediately above. Since "
                            + "sigma preserves the ordinate, it preserves the exact left-open, "
                            + "right-closed window zero less than Im rho and Im rho at most T. "
                            + "The source's multiplicity count is not formalized: the two supplied "
                            + "function identities prove pointwise zero stability but do not by "
                            + "themselves encode analytic orders of vanishing."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("critical-line-numerical-witness"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry."
                        + "critical_line_witness"),
                    H("One half plus three i is a fixed witness"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Rho, Sp, Colon, Eq, Sp, half, Sp, Plus, Sp, D(3), F.Id("i"),
                        Comma, Esc, MirrorSpec(Rho), Sp, Land, Sp,
                        Sigma(Rho), Sp, Eq, Sp, Rho, Sp, Land, Sp,
                        ImaginaryPart(Sigma(Rho)), Sp, Eq, Sp, D(3), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The on-line witness verifies all four structural laws, fixedness, and "
                        + "the preserved ordinate explicitly."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("off-line-numerical-witness"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry."
                        + "off_line_witness"),
                    H("Three quarters plus three i is an off-line witness"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Rho, Sp, Colon, Eq, Sp,
                        new Formula.Fraction(Num(3), Num(4)), Sp, Plus, Sp, D(3), F.Id("i"),
                        Comma, Esc, MirrorSpec(Rho), Sp, Land, Sp,
                        Sigma(Rho), Sp, Eq, Sp,
                        new Formula.Fraction(Num(1), Num(4)), Sp, Plus, Sp, D(3), F.Id("i"),
                        Sp, Land, Sp, Sigma(Rho), Sp, Neq, Sp, Rho, Sp, Land, Sp,
                        ImaginaryPart(Sigma(Rho)), Sp, Eq, Sp, D(3), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The off-line witness verifies all four structural laws, maps real part "
                        + "three quarters to one quarter, is not fixed, and retains ordinate "
                        + "three."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S3/Weil/ReflectionLedger")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S3/Zeros/CompletedZeta")),
            ]));
    }
}
