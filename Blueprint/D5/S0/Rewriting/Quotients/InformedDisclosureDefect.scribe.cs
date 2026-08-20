using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Quotients;

internal sealed class InformedDisclosureDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pair with identical disclosure and different consequences defeats every "
        + "disclosure-only distinction and rules out full consequence recovery.",
        H("Informed Disclosure Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("disclosure-collision-obstructs-informed-choice"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Quotients/InformedDisclosureDefect."
                    + "informed_disclosure_defect"),
                H("A disclosure collision obstructs fully informed choice"),
                StatementSource.FromAuthor(DisclosureDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The premise supplies two decision situations with the same disclosed "
                            + "value and different true consequences. A disclosure-only rule is "
                            + "an arbitrary function on disclosed values, so congruence forces it "
                            + "to return the same decision on this pair.")),
                    Paragraph(Text(
                        "Exact informedness in the source means a recovery function from the "
                            + "disclosure domain to the consequence domain. Such a function would "
                            + "send the equal disclosures to equal consequences, contradicting "
                            + "the witnessed consequence difference.")),
                    Paragraph(Text(
                        "Pinned Mathlib's congrArg is applied directly for the decision clause. "
                            + "Searches found adjacent fiber-factorization machinery but no exact "
                            + "theorem combining this universal decision limitation with the "
                            + "negated recovery factorization."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula DisclosureDefectFormula()
    {
        Formula situations = F.Id("Z");
        Formula disclosures = F.Id("B");
        Formula consequences = F.Id("Y");
        Formula decisions = F.Id("R");
        Formula disclosure = F.Id("D");
        Formula consequence = F.Id("K");
        Formula z = F.Id("z");
        Formula zp = F.Id("zprime");
        Formula rule = F.Id("rule");
        Formula recover = F.Id("recover");

        return Disp(Seq(
            Forall, Sp, situations, Comma, Sp, disclosures, Comma, Sp,
            consequences, Comma, Sp, decisions, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak,
            disclosure, Colon, Sp, situations, Sp, To, Sp, disclosures, Comma, Sp,
            consequence, Colon, Sp, situations, Sp, To, Sp, consequences, Comma, RowBreak,
            z, Comma, Sp, zp, Colon, Sp, situations, Comma, RowBreak,
            Apply(disclosure, z), Sp, Eq, Sp, Apply(disclosure, zp), Sp, Land, Sp,
            Apply(consequence, z), Sp, Neq, Sp, Apply(consequence, zp), Sp,
            Rightarrow, RowBreak,
            Open, Forall, Sp, rule, Colon, Sp, disclosures, Sp, To, Sp, decisions,
            Comma, Sp, Apply(rule, Apply(disclosure, z)), Sp, Eq, Sp,
            Apply(rule, Apply(disclosure, zp)), Close, Sp, Land, RowBreak,
            Neg, Sp, Exists, Sp, recover, Colon, Sp, disclosures, Sp, To, Sp,
            consequences, Comma, Sp, consequence, Sp, Eq, Sp,
            recover, Sp, Circ, Sp, disclosure, Dot));
    }
}
