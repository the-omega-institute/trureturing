using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Characterizations;

internal sealed class LocalPrecisionUnitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized p-adic precision equation has log p as its unique real unit.",
        H("The P-Adic Local Precision Unit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-p-adic-precision-has-one-logarithmic-unit"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Characterizations/LocalPrecisionUnit."
                        + "local_precision_unit_unique"),
                H("Normalized p-adic precision has one logarithmic unit"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The natural parameter p is required to be prime because it indexes the "
                            + "p-adic field. Its embedded p-adic norm is exactly p inverse under "
                            + "Mathlib's checked normalization. The theorem first states that log p "
                            + "satisfies the full two-equality equation, then separately states that "
                            + "every real value satisfying that equation equals log p. These are the "
                            + "existence and uniqueness halves of the source's word unique.")),
                    Paragraph(Text(
                        "A candidate real number represents only the source evaluation ell_p(p), "
                            + "rather than an otherwise unconstrained whole length function. "
                            + "Injectivity of the real exponential identifies this candidate with "
                            + "log p. Finally, the free exponent is quantified over the complex "
                            + "analytic domain, where the standard complex-power definition gives "
                            + "p to the negative s as exp of negative s times log p."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula p = F.Id("p");
        Formula ell = F.Id("ell");
        Formula s = F.Id("s");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula padics = Seq(Mathbb, Grp(F.Id("Q")), Underscore, Grp(p));
        Formula logP = Call("log", p);
        Formula padicP = Seq(Open, p, Colon, Sp, padics, Close);
        Formula normP = new Formula.Norm(padicP);
        Formula inverseP = Seq(p, Caret, Grp(Minus, D(1)));
        Formula normalizedAtLog = Seq(
            F.Id("e"), Caret, Grp(Minus, logP), Sp, Eq, Sp, normP,
            Sp, Land, Sp, normP, Sp, Eq, Sp, inverseP);
        Formula normalizedAtEll = Seq(
            F.Id("e"), Caret, Grp(Minus, ell), Sp, Eq, Sp, normP,
            Sp, Land, Sp, normP, Sp, Eq, Sp, inverseP);
        Formula uniqueness = Seq(
            Forall, Sp, ell, Sp, InMacro, Sp, reals, Comma, Sp,
            Open, normalizedAtEll, Close, Sp, Rightarrow, Sp,
            ell, Sp, Eq, Sp, logP);
        Formula complexWeight = Seq(
            Forall, Sp, s, Sp, InMacro, Sp, complexes, Comma, Sp,
            p, Caret, Grp(Minus, s), Sp, Eq, Sp,
            F.Id("e"), Caret, Grp(Minus, s, Sp, logP));

        return Disp(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, naturals, Comma, Sp,
            p, Sp, F.Text, Grp(Sp, F.Id("prime")), Comma, RowBreak,
            Open,
                Open, Open, normalizedAtLog, Close, Sp, Land, Sp,
                    Open, uniqueness, Close, Close,
                Sp, Land, RowBreak,
                Open, complexWeight, Close,
            Close, Dot));
    }
}
