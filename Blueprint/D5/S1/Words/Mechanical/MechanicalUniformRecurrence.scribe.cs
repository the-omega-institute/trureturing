using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalUniformRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prove uniform recurrence for lower mechanical words at every irrational slope.",
        H("Uniform Recurrence of Irrational Lower Mechanical Words"),
        Blocks(
            Paragraph(Text(
                "Fix an irrational real slope alpha in the half-open interval from zero to one, "
                + "an arbitrary real intercept rho, and a finite factor that occurs at a natural "
                + "starting index.")),
            Describe.Lean(
                DescribeId.Create("irrational-lower-mechanical-uniform-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalUniformRecurrence."
                    + "lower_mechanical_factor_uniformly_recurrent"),
                H("Every occurring factor returns within one uniform window bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Alpha, Comma, Sp, Rho, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Sp, Leq, Sp, Alpha, Sp, Lt, Sp, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close,
                    Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Forall, Sp, F.Id("w"), InMacro, Sp,
                    F.Id("FactorSet"), Open, Alpha, Comma, Sp, Rho, Comma, Sp,
                    F.Id("n"), Close, Comma, Sp,
                    Esc, Exists, Sp, F.Id("R"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Forall, Sp, F.Id("i"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Esc, Exists, Sp, F.Id("j"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("i"), Sp, Leq, Sp, F.Id("j"), Sp, Land, Sp,
                    F.Id("j"), Sp, Plus, Sp, F.Id("n"), Sp, Leq, Sp,
                    F.Id("i"), Sp, Plus, Sp, F.Id("R"), Sp, Land, Sp,
                    F.Id("w"), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("lowerMechanicalFactor")), Open,
                    Alpha, Comma, Sp, Rho, Comma, Sp, F.Id("n"), Comma, Sp,
                    F.Id("j"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a witnessing start, choose a real phase interval immediately to the "
                        + "right and stop before both the next finite coding breakpoint and one. "
                        + "The lower word uses a half-open threshold, so every phase in this "
                        + "right-sided interval has the same prefix counts and therefore the same "
                        + "factor.")),
                    Paragraph(Text(
                        "The interval maps to an open arc of the additive circle without crossing "
                        + "the quotient seam. Irrational rotation makes the forward orbit from "
                        + "every circle point meet that arc. Compactness supplies a finite subcover "
                        + "by inverse translates, and the largest translate index bounds every "
                        + "waiting time.")),
                    Paragraph(Text(
                        "For an arbitrary intercept, equality on the circle is returned to the "
                        + "canonical real phase by the unique representative in the half-open "
                        + "interval from zero to one. Adding the factor length to the waiting-time "
                        + "bound places the entire returned factor inside the asserted window."))),
                DescribeRole.Theorem))));
}
