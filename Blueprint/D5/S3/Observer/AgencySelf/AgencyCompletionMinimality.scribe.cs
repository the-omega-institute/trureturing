using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class AgencyCompletionMinimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencySelf/AgencyCompletionMinimality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Componentwise recoverability induces recoverability of the paired agency completion.",
        H("Agency Completion Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("component-factorizations-induce-a-paired-factorization"),
                DeclarationHandle.Create(
                    Prefix + "paired_completion_factors_through_summary"),
                H("Component factorizations induce a paired factorization"),
                StatementSource.FromAuthor(FactorizationStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume both the current-memory readout and the strategy profile factor "
                            + "pointwise through the same summary.")),
                    Paragraph(Text(
                        "Pair the two supplied factor maps. This yields a factor from summaries "
                            + "to memory-profile pairs through which the paired completion equals "
                            + "the composite with the summary.")),
                    Paragraph(Text(
                        "The conclusion asserts existence of that paired factor; it does not "
                            + "claim uniqueness or a converse factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-paired-completion-recovers-both-components"),
                DeclarationHandle.Create(Prefix + "paired_completion_recovers_components"),
                H("The paired completion recovers both components"),
                StatementSource.FromAuthor(RecoveryStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary current and profile readouts, pair their values at each "
                            + "history.")),
                    Paragraph(Text(
                        "The first and second product projections recover the current and profile "
                            + "functions respectively, with no extra assumptions."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Product() => Call("Prod", F.Id("M"), F.Id("P"));

    private static Formula PairReadout() => Seq(
        F.Id("h"), Sp, Mapsto, Sp,
        Open, Call("current", F.Id("h")), Comma, Sp,
        Call("profile", F.Id("h")), Close);

    private static Formula FactorizationStatement()
    {
        Formula h = F.Id("h");
        Formula currentFactors = Seq(
            Forall, Sp, h, Colon, Sp, F.Id("H"), Comma, Sp,
            Call("current", h), Sp, Eq, Sp,
            Call("currentFactor", Call("summary", h)));
        Formula profileFactors = Seq(
            Forall, Sp, h, Colon, Sp, F.Id("H"), Comma, Sp,
            Call("profile", h), Sp, Eq, Sp,
            Call("profileFactor", Call("summary", h)));
        Formula consequence = Seq(
            Exists, Sp, F.Id("pairFactor"), Colon, Sp,
            Arrow(F.Id("S"), Product()), Comma, Sp,
            PairReadout(), Sp, Eq, Sp,
            F.Id("pairFactor"), Sp, Circ, Sp, F.Id("summary"));
        return Disp(Seq(
            Forall, Sp, F.Id("current"), Colon, Sp,
            Arrow(F.Id("H"), F.Id("M")), Comma, Sp,
            F.Id("profile"), Colon, Sp, Arrow(F.Id("H"), F.Id("P")), Comma,
            RowBreak, Grp(),
            F.Id("summary"), Colon, Sp, Arrow(F.Id("H"), F.Id("S")), Comma, Sp,
            F.Id("currentFactor"), Colon, Sp, Arrow(F.Id("S"), F.Id("M")),
            Comma, RowBreak, Grp(),
            F.Id("profileFactor"), Colon, Sp, Arrow(F.Id("S"), F.Id("P")),
            Comma, RowBreak, Grp(),
            Open, currentFactors, Sp, Land, Sp, profileFactors, Close,
            Sp, Rightarrow, Sp, consequence, Dot));
    }

    private static Formula RecoveryStatement()
    {
        Formula currentProjection = Seq(
            F.Id("h"), Sp, Mapsto, Sp,
            Call("fst", Call("pair", Call("current", F.Id("h")),
                Call("profile", F.Id("h")))));
        Formula profileProjection = Seq(
            F.Id("h"), Sp, Mapsto, Sp,
            Call("snd", Call("pair", Call("current", F.Id("h")),
                Call("profile", F.Id("h")))));
        Formula consequence = Seq(
            currentProjection, Sp, Eq, Sp, F.Id("current"), Sp, Land, Sp,
            profileProjection, Sp, Eq, Sp, F.Id("profile"));
        return Disp(Seq(
            Forall, Sp, F.Id("current"), Colon, Sp,
            Arrow(F.Id("H"), F.Id("M")), Comma, Sp,
            F.Id("profile"), Colon, Sp, Arrow(F.Id("H"), F.Id("P")), Comma, Sp,
            Open, consequence, Close, Dot));
    }
}
