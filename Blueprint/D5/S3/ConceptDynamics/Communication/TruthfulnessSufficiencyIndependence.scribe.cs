using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class TruthfulnessSufficiencyIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Truthful reporting and target sufficiency jointly yield a sufficient sent report, "
            + "while neither condition implies the other.",
        H("Truthfulness and Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truthfulness-sufficiency-independence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Communication/"
                        + "TruthfulnessSufficiencyIndependence."
                        + "truthfulness_sufficiency_independence"),
                H("Reporting honesty and sufficiency are independent factors"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A report profile publicly contains a target on states, the report that "
                            + "the state warrants, the report actually sent, and a decoder from "
                            + "messages to target values.")),
                    Paragraph(Text(
                        "Equality of the sent and truthful mechanisms transports a factorization "
                            + "through the truthful mechanism to the sent mechanism. This is the "
                            + "forward trust clause.")),
                    Paragraph(Text(
                        "Four concrete finite profiles establish the two independent axes. A Unit "
                            + "message space is honest but too coarse; a Boolean identity report "
                            + "with a negated sent message is sufficient but dishonest; identity "
                            + "mechanisms satisfy both; and distinct constant reports with a varying "
                            + "target satisfy neither.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact report-factorization "
                            + "theorem. Loogle missed, and LeanSearch returned only probabilistic "
                            + "notions of independence."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Sup(Formula value, Formula index) =>
        Seq(value, Caret, Grp(index));

    private static Formula Composition(Formula decoder, Formula report) =>
        Seq(decoder, Sp, Circ, Sp, report);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State"), message = F.Id("Message"),
            targetType = F.Id("Target");
        Formula profile = F.Id("profile");
        Formula target = Sup(F.Id("T"), profile);
        Formula decoder = Sup(OverlineTarget(), profile);
        Formula sent = Sup(Sub(F.Id("R"), F.Id("send")), profile);
        Formula truthful = Sup(Sub(F.Id("R"), F.Id("true")), profile);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")), Caret, Grp(Star));
        Formula honest = Seq(sent, Sp, Eq, Sp, truthful);
        Formula sufficient = Seq(target, Sp, Eq, Sp, Composition(decoder, truthful));
        Formula sentSufficient = Seq(target, Sp, Eq, Sp, Composition(decoder, sent));
        Formula honestOnly = ProfileClause(F.Id("h"), true, false, true);
        Formula sufficientOnly = ProfileClause(F.Id("s"), false, true, false);
        Formula both = ProfileClause(F.Id("b"), true, true, false);
        Formula neither = ProfileClause(F.Id("n"), false, false, false);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, message, Comma, Sp, targetType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            profile, Colon, Sp, Call("ReportProfile", state, message, targetType),
            Comma, RowBreak, Grp(),
            Open, honest, Sp, Rightarrow, Sp, sufficient, Sp, Rightarrow, Sp,
            sentSufficient, Close, Sp, Land, RowBreak, Grp(),
            Open, honestOnly, Close, Sp, Land, RowBreak, Grp(),
            Open, sufficientOnly, Close, Sp, Land, RowBreak, Grp(),
            Open, both, Close, Sp, Land, RowBreak, Grp(),
            Open, neither, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ProfileClause(
        Formula profile, bool isHonest, bool isSufficient, bool unitMessage)
    {
        Formula target = Sup(F.Id("T"), profile);
        Formula decoder = Sup(OverlineTarget(), profile);
        Formula sent = Sup(Sub(F.Id("R"), F.Id("send")), profile);
        Formula truthful = Sup(Sub(F.Id("R"), F.Id("true")), profile);
        Formula honestyRelation = Seq(sent, Sp,
            isHonest ? Eq : Neq, Sp, truthful);
        Formula sufficiencyRelation = Seq(target, Sp,
            isSufficient ? Eq : Neq, Sp, Composition(decoder, truthful));

        return Seq(
            Exists, Sp, profile, Colon, Sp,
            Call("ReportProfile", F.Id("Bool"),
                unitMessage ? F.Id("Unit") : F.Id("Bool"),
                F.Id("Bool")), Comma, Sp,
            honestyRelation, Sp, Land, Sp, sufficiencyRelation);
    }

    private static Formula OverlineTarget() =>
        Seq(Overline, Grp(F.Id("T")));
}
