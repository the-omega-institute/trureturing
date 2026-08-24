using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.FamilySums;

internal sealed class TermBoundDoesNotBoundFamilySumDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Growing finite families can keep a nonzero sum despite vanishing term bounds.",
        H("Term Bounds Do Not Bound Growing Family Sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("term-bound-does-not-bound-family-sum"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/FamilySums/"
                        + "TermBoundDoesNotBoundFamilySum."
                        + "term_bound_does_not_bound_family_sum"),
                H("Small terms do not force a growing family sum to vanish"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every given positive natural exponent gamma, the witness takes "
                            + "epsilon_m equal to 1/(m+1), a family of (m+1)^gamma members, "
                            + "and identical amplitudes epsilon_m^gamma. The scale is positive "
                            + "and tends to zero, and every amplitude meets the bound with equality.")),
                    Paragraph(Text(
                        "Summing the (m+1)^gamma absolute amplitudes gives exactly one for every m. "
                            + "The family sums are therefore bounded away from zero and cannot "
                            + "converge to zero, even though the individual bound vanishes.")),
                    Paragraph(Text(
                        "A separate Lean example fixes the family size at one and verifies "
                            + "that its sum does converge to zero. This distinguishes the "
                            + "growth obstruction from a universal failure of termwise decay.")),
                    Paragraph(Text(
                        "The source's six controls, covering analytic gain, object counts, "
                            + "cancellation grouping, cut termination, truncation remainders, "
                            + "and time-block accumulation, are a research checklist rather "
                            + "than mathematical assertions and are not encoded as propositions."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Absolute(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula i = F.Id("i");
        Formula gamma = GammaLower;
        Formula epsilon = Varepsilon;
        Formula familySize = F.Id("n");
        Formula amplitude = F.Id("A");
        Formula epsilonM = Subscript(epsilon, m);
        Formula familySizeM = Subscript(familySize, m);
        Formula amplitudeMI = Subscript(amplitude, Seq(m, Comma, i));
        Formula familySum = Seq(
            Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", familySizeM)), Sp,
            Absolute(amplitudeMI));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Forall, Sp, gamma, InMacro, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, gamma, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp,
            epsilon, Colon, Sp, naturals, To, reals, Comma, Sp,
            familySize, Colon, Sp, naturals, To, naturals, Comma, Sp,
            amplitude, Colon, Sp, Forall, Sp, m, Comma, Sp,
            Call("Fin", familySizeM), To, reals, Comma, RowBreak, Grp(),
            Lim, Underscore, Grp(m, To, Infty), Sp, epsilonM, Sp, Eq, Sp, D(0),
            Sp, Land, Sp,
            Forall, Sp, m, Comma, Sp, D(0), Sp, Lt, Sp, epsilonM,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, m, Comma, Sp, i, InMacro, Call("Fin", familySizeM),
            Comma, Sp, Absolute(amplitudeMI), Sp, Leq, Sp,
            epsilonM, Caret, Grp(gamma), Sp, Land, RowBreak, Grp(),
            Forall, Sp, m, Comma, Sp, familySum, Sp, Eq, Sp, D(1),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open, Lim, Underscore, Grp(m, To, Infty), Sp,
            familySum, Sp, Eq, Sp, D(0), Close, Dot));
    }
}
