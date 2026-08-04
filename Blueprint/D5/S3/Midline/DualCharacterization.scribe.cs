using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class DualCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/DualCharacterization",
            "Mirror fixed points and unitary half-density parameters define the same midline."),
        H("Dual Characterization of the Critical Midline"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("mirror-fixed-points-and-unitary-parameters-define-the-critical-midline"),
                H("Mirror fixed points and unitary parameters define the critical midline"),
                LeanTheorem(
                    "D5/S3/Midline/DualCharacterization.midline_dual_characterization"),
                Disp(Seq(Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Open, Exists, Sp, F.Id("a"), Comma, Ell, Open, F.Id("a"), Close, Neq, Sp, D(0), Close, Sp, Rightarrow, Sp, Open, OpenBrace, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Colon, Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close, Eq, F.Id("s"), CloseBrace, Eq, OpenBrace, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Colon, Forall, Sp, F.Id("a"), Comma, Vert, Operatorname, Grp(F.Id("halfDensityReading")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Vert, Eq, D(1), CloseBrace, Esc, Land, Esc, OpenBrace, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Colon, Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close, Eq, F.Id("s"), CloseBrace, Eq, OpenBrace, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Colon, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), CloseBrace, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For any additive ledger with at least one nonzero length, the set of "
                    + "conjugate-reflection fixed points equals both the set of parameters whose "
                    + "half-density readings all have unit norm and the line of parameters with "
                    + "real part one half. This set-level theorem is derived from the existing "
                    + "pointwise critical-line characterizations. It locates no zeta zero and "
                    + "asserts no Riemann-hypothesis conclusion.")))))));
}
