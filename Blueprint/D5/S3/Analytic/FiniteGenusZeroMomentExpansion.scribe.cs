using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class FiniteGenusZeroMomentExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite genus-zero factors admit an exact central-moment expansion with remainder.",
        H("Finite Genus-Zero Central-Moment Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-logarithmic-sums-have-an-exact-moment-expansion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/FiniteGenusZeroMomentExpansion."
                    + "centralLogSum_eq_momentExpansion_add_remainder"),
                H("Finite logarithmic sums have an exact moment expansion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let s be a finite index set, let v_j be complex nodes with natural "
                        + "multiplicities m_j, and fix a complex argument w. If every factor "
                        + "1 + v_j w is nonzero, then the associated finite logarithmic sum "
                        + "equals its central-moment expansion through every order K plus the "
                        + "displayed exact geometric remainder. The case K = 0 is included: the "
                        + "empty moment sum vanishes and the remainder is the original sum.")),
                    Paragraph(Text(
                        "The source atom states an infinite genus-zero canonical product and an "
                        + "infinite Taylor expansion. Those claims require convergence and order "
                        + "infrastructure that the atom does not supply. The deposited theorem "
                        + "therefore records the finite algebraic core without claiming analytic "
                        + "convergence; its explicit remainder retains the full finite content.")),
                    Paragraph(Text(
                        "Six-route repository searches found no equivalent D5 declaration. The "
                        + "pinned library was also searched first and supplies the product "
                        + "logarithmic-derivative rule, the power rule, the finite geometric-sum "
                        + "identity, and finite-sum commutation. The proof applies those results "
                        + "directly and makes the nonzero denominator condition explicit."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula j = F.Id("j");
        Formula n = F.Id("n");
        Formula s = F.Id("s");
        Formula v = F.Id("v");
        Formula m = F.Id("m");
        Formula w = F.Id("w");
        Formula k = F.Id("K");
        Formula vj = F.Seq(v, F.Underscore, j);
        Formula mj = F.Seq(m, F.Underscore, j);
        Formula denominator = F.Seq(F.D(1), F.Plus, vj, F.Sp, F.Cdot, F.Sp, w);
        Formula weightedNode = F.Seq(mj, F.Sp, F.Cdot, F.Sp, vj);
        Formula nodeRange = F.Grp(j, F.InMacro, F.Sp, s);
        Formula orderRange = F.Grp(
            F.D(0), F.Sp, F.Leq, F.Sp, n, F.Sp, F.Lt, F.Sp, k);
        Formula hypothesis = F.Seq(
            F.Forall, F.Sp, j, F.InMacro, F.Sp, s, F.Comma, F.Sp,
            denominator, F.Sp, F.Neq, F.Sp, F.D(0));
        Formula logarithmicSum = F.Seq(
            F.Sum, F.Underscore, nodeRange, F.Sp,
            F.Frac, F.Grp(weightedNode), F.Grp(denominator));
        Formula moment = F.Seq(
            F.Sum, F.Underscore, nodeRange, F.Sp,
            mj, F.Sp, F.Cdot, F.Sp, vj, F.Caret, F.Grp(n, F.Plus, F.D(1)));
        Formula momentExpansion = F.Seq(
            F.Sum, F.Underscore, orderRange, F.Sp,
            F.Grp(F.Minus, F.D(1)), F.Caret, F.Grp(n), F.Sp, F.Cdot, F.Sp,
            F.Grp(moment), F.Sp, F.Cdot, F.Sp, w, F.Caret, F.Grp(n));
        Formula remainder = F.Seq(
            F.Sum, F.Underscore, nodeRange, F.Sp,
            F.Frac,
            F.Grp(
                weightedNode, F.Sp, F.Cdot, F.Sp,
                F.Grp(F.Minus, vj, F.Sp, F.Cdot, F.Sp, w), F.Caret, F.Grp(k)),
            F.Grp(denominator));

        return F.Disp(F.Seq(
            F.Grp(hypothesis), F.Sp, F.Rightarrow, F.Sp, RowBreak, F.Grp(),
            logarithmicSum, F.Sp, F.Eq, F.Sp,
            momentExpansion, F.Sp, F.Plus, F.Sp, remainder, F.Dot));
    }
}
