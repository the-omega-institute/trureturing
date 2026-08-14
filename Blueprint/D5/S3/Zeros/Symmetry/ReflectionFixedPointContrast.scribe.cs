using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class ReflectionFixedPointContrastDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var half = new Formula.Fraction(Num(1), Num(2));
        var reflectionFixed = Seq(
            Operatorname, Grp(F.Id("reflection")), Open, F.Id("s"), Close,
            Sp, Eq, Sp, F.Id("s"));
        var mirrorFixed = Seq(
            Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close,
            Sp, Eq, Sp, F.Id("s"));
        var complexSet = Seq(F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Colon);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Plain reflection fixes one point, while conjugate reflection fixes the critical line.",
            H("Reflection Fixed-Point Contrast"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("plain-reflection-fixes-one-half"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast.reflection_fixed_iff"),
                    H("Plain reflection fixes exactly one half"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")),
                        Comma, Esc, reflectionFixed, Sp, Leftrightarrow, Sp,
                        F.Id("s"), Sp, Eq, Sp, half, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every complex parameter, the frozen plain reflection s maps to one "
                        + "minus s fixes s exactly when s is one half. This is the point half of "
                        + "the source's point-versus-line contrast."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("reflection-and-mirror-fixed-loci-contrast"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast."
                        + "reflection_mirror_fixed_locus_contrast"),
                    H("Reflection and mirror fixed loci contrast"),
                    StatementSource.FromAuthor(Disp(Seq(
                        OpenBrace, complexSet, reflectionFixed, CloseBrace,
                        Sp, Eq, Sp, OpenBrace, half, CloseBrace,
                        Sp, Land, Sp,
                        OpenBrace, complexSet, mirrorFixed, CloseBrace,
                        Sp, Eq, Sp,
                        OpenBrace, complexSet, Re, Open, F.Id("s"), Close,
                        Sp, Eq, Sp, half, CloseBrace))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The first equality packages the point characterization as a singleton "
                            + "fixed set. The second equality is obtained directly from the frozen "
                            + "midline dual characterization, so conjugate reflection fixes every "
                            + "complex parameter with real part one half.")),
                        Paragraph(Text(
                            "This declaration closes only the critical-line-existence subitem. It "
                            + "does not assert information-flow increments, information conservation, "
                            + "Wigner's dichotomy, an antiunitary-forcing mechanism, Lambda's numerical "
                            + "certificate, coexistence of the two information layers, or that zeta "
                            + "zeros lie on the fixed line."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S3/Midline/DualCharacterization")),
            ]));
    }
}
