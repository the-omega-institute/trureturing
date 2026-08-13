using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class IndependentKillRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent coverage and visibility events give a product kill rate.",
        H("Independent Kill Rate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-kill-rate"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/IndependentKillRate.independent_kill_rate"),
                H("Independent event rates multiply"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Outcome"), Comma, Sp,
                    Operatorname, Grp(F.Id("MeasurableSpace")), Open,
                    F.Id("Outcome"), Close, Comma, Sp,
                    F.Id("mu"), Colon, Sp,
                    Operatorname, Grp(F.Id("Measure")), Open, F.Id("Outcome"), Close,
                    Comma, Sp,
                    F.Id("C"), Comma, Sp, F.Id("V"), Colon, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("Outcome"), Close,
                    Comma, Sp,
                    F.Id("coverageRate"), Comma, Sp, F.Id("visibilityRate"), Colon, Sp,
                    Operatorname, Grp(F.Id("ENNReal")), Comma, Sp,
                    Open,
                    Operatorname, Grp(F.Id("IndepSet")), Open,
                    F.Id("C"), Comma, Sp, F.Id("V"), Comma, Sp, F.Id("mu"), Close,
                    Sp, Land, Sp,
                    F.Id("mu"), Open, F.Id("C"), Close,
                    Sp, Eq, Sp, F.Id("coverageRate"),
                    Sp, Land, Sp,
                    F.Id("mu"), Open, F.Id("V"), Close,
                    Sp, Eq, Sp, F.Id("visibilityRate"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("mu"), Open,
                    Operatorname, Grp(F.Id("inter")), Open,
                    F.Id("C"), Comma, Sp, F.Id("V"), Close, Close,
                    Sp, Eq, Sp,
                    F.Id("coverageRate"), Sp, Times, Sp, F.Id("visibilityRate"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be the coverage event and V the visibility event in a measured "
                        + "outcome space. If the events are independent, and their measures are "
                        + "coverageRate and visibilityRate, then the measure of their intersection "
                        + "is the product of those two rates.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched first for independent events and intersection "
                        + "measures. ProbabilityTheory.IndepSet.measure_inter_eq_mul was an exact "
                        + "hit, and ProbabilityTheory.indepSet_iff_measure_inter_eq_mul was a "
                        + "related hit. No existing D5 declaration stated this measure-theoretic "
                        + "event identity. The Lean theorem is a thin wrapper around the exact hit, "
                        + "followed only by rewriting the two named rates.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the source clause identifying killing "
                        + "with the intersection of independent coverage and visibility events. "
                        + "The finite parameter interpretation, regression interpretation, multi-site "
                        + "mutations, and biased behavior remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
