using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Fusion;

internal sealed class GroupQuotientInformationLossDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite free group quotient loses exactly the conditional information in its residual coordinate.",
        H("Information Loss under a Finite Free Group Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-free-group-quotient-information-loss"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Fusion/GroupQuotientInformationLoss."
                        + "group_quotient_information_loss"),
                H("Finite free group quotient information loss"),
                StatementSource.FromAuthor(InformationLossFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite group G act freely on a finite set Y. A chosen section s "
                            + "of the genuine orbit quotient B = Y/G determines the equivalence "
                            + "c_s : Y equiv B x G used by the Lean declaration. For a PMF Z, "
                            + "write Z_B for its quotient pushforward and Z_s for its pushforward "
                            + "along c_s. Entropy is the repository finite Shannon entropy of the "
                            + "real mass underlying the PMF.")),
                    Paragraph(Text(
                        "The first two conjuncts are respectively the Shannon chain rule in the "
                            + "quotient-residual coordinates and its information-loss rearrangement. "
                            + "The third is only an implication: attaining log(card G) forces every "
                            + "positive-mass conditional residual law of Z to be uniform. It does not "
                            + "assert the converse or constrain zero-mass fibers.")),
                    Paragraph(Text(
                        "For arbitrary PMFs P and Q, the fourth conjunct is the unrestricted "
                            + "extended-nonnegative-real Kullback-Leibler chain rule. Its conditional "
                            + "divergences are weighted by the P quotient marginal. No positivity or "
                            + "absolute-continuity premise is added; infinite divergence is allowed.")),
                    Paragraph(Text(
                        "The fifth conjunct names the quotient data-processing loss as total KL "
                            + "minus quotient KL and identifies it with the same weighted conditional "
                            + "divergence. Under the classical extended-value convention this "
                            + "subtraction identity is asserted when the quotient KL is finite, so "
                            + "the undefined infinity-minus-infinity case is not silently collapsed."))),
                DescribeRole.Theorem))));

    private static Formula At(Formula family, Formula argument) =>
        Seq(family, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula subscript) =>
        Seq(value, Underscore, Grp(subscript));

    private static Formula Entropy(Formula law) => Call("H", law);

    private static Formula Divergence(Formula left, Formula right) =>
        Seq(F.Id("D"), Open, left, Sp, Vert, Sp, right, Close);

    private static Formula Uniform(Formula group) =>
        Call("Unif", group);

    private static Formula InformationLossFormula()
    {
        Formula group = F.Id("G"), source = F.Id("Y"), quotient = F.Id("B");
        Formula section = F.Id("s"), z = F.Id("Z"), p = F.Id("P"), q = F.Id("Q");
        Formula b = F.Id("b");
        Formula zQuotient = Subscript(z, quotient);
        Formula pQuotient = Subscript(p, quotient);
        Formula qQuotient = Subscript(q, quotient);
        Formula zConditional = Subscript(z, Seq(Gamma, Bar, b));
        Formula pConditional = Subscript(p, Seq(Gamma, Bar, b));
        Formula qConditional = Subscript(q, Seq(Gamma, Bar, b));
        Formula conditionalEntropy = Call("Hcond", Subscript(z, F.Id("s")));
        Formula loss = Seq(Entropy(z), Sp, Minus, Sp, Entropy(zQuotient));
        Formula quotientDivergence = Divergence(pQuotient, qQuotient);
        Formula conditionalDivergence = Seq(
            Sum, Underscore, Grp(b), At(pQuotient, b), Sp, Cdot, Sp,
            Divergence(pConditional, qConditional));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, source, Comma, Sp,
            Call("FiniteGroup", group), Sp, Land, Sp,
            Call("Finite", source), Sp, Land, Sp,
            Call("FreeAction", group, source), Comma, RowBreak,
            quotient, Sp, Eq, Sp, Seq(source, Slash, group), Comma, Sp,
            section, Colon, Sp, quotient, Sp, To, Sp, source, Comma, Sp,
            Call("section", section), Comma, RowBreak,
            z, Comma, Sp, p, Comma, Sp, q, Colon, Sp, Call("PMF", source), Sp,
            Rightarrow, RowBreak,
            Entropy(z), Sp, Eq, Sp,
            Entropy(zQuotient), Sp, Plus, Sp, conditionalEntropy, Sp,
            Land, RowBreak,
            loss, Sp, Eq, Sp, conditionalEntropy, Sp,
            Land, RowBreak,
            Open, loss, Sp, Eq, Sp, Log, Open, Call("card", group), Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, b, Comma, Sp, At(zQuotient, b), Sp, Neq, Sp, D(0),
            Sp, Rightarrow, Sp, zConditional, Sp, Eq, Sp, Uniform(group), Close,
            Sp, Land, RowBreak,
            Divergence(p, q), Sp, Eq, Sp,
            quotientDivergence, Sp, Plus, Sp, conditionalDivergence,
            Sp, Land, RowBreak,
            Open, quotientDivergence, Sp, Neq, Sp, Infty,
            Sp, Rightarrow, Sp,
            Divergence(p, q), Sp, Minus, Sp, quotientDivergence,
            Sp, Eq, Sp, conditionalDivergence, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
