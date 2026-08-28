using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class RiemannHypothesisScatteringResonanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula quarter = new Formula.Fraction(Num(1), Num(4));
        Formula half = new Formula.Fraction(Num(1), Num(2));
        Formula threeQuarters = new Formula.Fraction(Num(3), Num(4));
        Formula s = F.Id("s");
        Formula rho = Rho;
        Formula resonance = Seq(F.Id("s"), Underscore, Grp(rho));
        Formula phiAtS = Seq(Phi, Open, s, Close);
        Formula phiAtReflection = Seq(Phi, Open, D(1), Minus, s, Close);
        Formula poleAtS = Seq(
            Operatorname, Grp(F.Id("Pole")), Underscore, Grp(Phi), Open, s, Close);
        Formula zeroAtS = Seq(
            Operatorname, Grp(F.Id("Zero")), Underscore, Grp(Phi), Open, s, Close);
        Formula reflectedZero = Seq(
            Operatorname, Grp(F.Id("Zero")), Underscore, Grp(Phi),
            Open, D(1), Minus, resonance, Close);

        Formula statement = Seq(
            Begin, Grp(F.Id("gathered")),
            Open, F.Id("RH"), Sp, Leftrightarrow, Sp,
            Forall, Sp, s, InMacro, Sp, complex, Comma, Esc,
            poleAtS, Sp, Rightarrow, Sp, Re, Open, s, Close, Eq, quarter, Close,
            Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("EventuallyEq")), Underscore,
            Grp(Operatorname, Grp(F.Id("codiscrete")), Open, complex, Close),
            Open, phiAtS, phiAtReflection, Comma, Sp, D(1), Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, rho, InMacro, Sp, complex, Comma, Esc,
            Operatorname, Grp(F.Id("IsNontrivialZero")), Open, rho, Close,
            Sp, Rightarrow, Sp, reflectedZero, Close,
            Sp, Land, RowBreak,
            Open, F.Id("RH"), Sp, Leftrightarrow, Sp,
            Forall, Sp, s, InMacro, Sp, complex, Comma, Esc,
            zeroAtS, Sp, Rightarrow, Sp, Re, Open, s, Close, Eq, threeQuarters, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, rho, InMacro, Sp, complex, Comma, Esc,
            Re, Open, rho, Close, Eq, half, Sp, Rightarrow, Sp,
            Re, Open, resonance, Close, Eq, quarter, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, rho, InMacro, Sp, complex, Comma, Esc,
            Re, Open, rho, Close, Eq, half, Sp, Rightarrow, Sp,
            Re, Open, D(1), Minus, resonance, Close, Eq, threeQuarters, Close,
            Dot, Sp, End, Grp(F.Id("gathered")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The Riemann hypothesis is equivalent to the quarter-line scattering resonance "
                + "condition and to its reflected three-quarter-line antiresonance condition.",
            H("Riemann Hypothesis in Scattering Resonance Coordinates"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create(
                        "riemann-hypothesis-scattering-resonance-form"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/Scattering/RiemannHypothesisScatteringResonance."
                        + "riemann_hypothesis_scattering_resonance_form"),
                    H("RH has the quarter-line resonance and three-quarter-line zero forms"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Here Phi(s) is the concrete completed-zeta ratio "
                            + "Lambda(2s-1)/Lambda(2s). Pole_Phi(s) means that its completed-zeta "
                            + "denominator vanishes, Zero_Phi(s) means that its numerator vanishes, "
                            + "and s_rho is rho/2. These are the named Lean definitions, not "
                            + "abstract replacement carriers.")),
                        Paragraph(Text(
                            "The displayed conjunction retains all six Lean leaves. Both RH "
                            + "biconditionals contribute their forward and reverse assertions; the "
                            + "last two leaves separately retain the resonance and antiresonance "
                            + "coordinates of the final boxed split.")),
                        Paragraph(Text(
                            "The product Phi(s)Phi(1-s)=1 is stated as an eventual equality on the "
                            + "codiscrete complex filter. This is the Lean formulation of the "
                            + "meromorphic identity: it removes only the discrete zero and pole "
                            + "locus, rather than falsely asserting an equality of totalized "
                            + "division values at exceptional points.")),
                        Paragraph(Text(
                            "The reflected-zero leaf uses the completed-zeta functional equation. "
                            + "The two reverse implications additionally use the pinned exterior "
                            + "zero-free theorems and Gamma-factor zero classification to recover "
                            + "mathlib's full RiemannHypothesis predicate."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S3/Weil/Scattering/CompletedZetaScatteringCollapse")),
            ]));
    }
}
