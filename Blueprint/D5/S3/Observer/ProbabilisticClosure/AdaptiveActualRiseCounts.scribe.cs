using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class AdaptiveActualRiseCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula space = F.Id("U");
        Formula policy = F.Id("p");
        Formula seed = F.Id("u");
        Formula source = F.Id("z");
        Formula time = F.Id("T");
        Formula side = F.Id("s");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula previous = Seq(time, Minus, D(1));
        Formula count = Call("actualRiseCount", policy, seed, source, side, time);
        Formula countPrevious = Call("actualRiseCount", policy, seed, source, side, previous);
        Formula length = Call("sideCount", Call("zeroReplay", policy, seed, previous), side);
        Formula half = Seq(Lfloor, Frac, Grp(length), Grp(D(2)), Rfloor);
        Formula halfUp = Seq(Lfloor, Frac, Grp(Seq(length, Plus, D(1))), Grp(D(2)), Rfloor);
        Formula root = Call("root", source);
        Formula exponent = Seq(Operatorname, Grp(F.Id("if")), Sp, root,
            Sp, Operatorname, Grp(F.Id("then")), Sp, half,
            Sp, Operatorname, Grp(F.Id("else")), Sp, halfUp);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, space, Colon, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("MeasurableSpace", space), CloseBracket, Comma,
            RowBreak, Grp(),
            Forall, Sp, policy, Colon, Call("Policy", space), Comma, Sp,
            Forall, Sp, seed, Colon, space, Comma, Sp,
            Forall, Sp, source, Colon, F.Id("Source"), Comma, Sp,
            Forall, Sp, time, InMacro, naturals, Comma,
            RowBreak, Grp(),
            Open, Call("noAdjacentOnes", source), Land,
            Call("stoppingTime", policy, seed, source), Eq, time, Close,
            Rightarrow, Open,
            D(0), Lt, time, Land, Open, Forall, Sp, side, Colon, F.Id("Bool"), Comma,
            RowBreak, Grp(),
            Open, count, Eq, countPrevious, Close, Land,
            Open, count, Eq, exponent, Close, Close, Close,
            End, Grp(F.Id("gathered"))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual acquired 01 transitions in an absorbing adaptive two-arm execution.",
            H("Chronological rise counts at the first marker"),
            Blocks(Describe.Lean(
                DescribeId.Create("actual-rise-count-at-first-stop"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts.actual_rise_count_at_first_stop"),
                H("Actual rises equal preterminal alternating half-lengths"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Source, Policy, actualRun, sideCount, zeroReplay and stoppingTime are those of AdaptiveMarkerStoppingTails. "
                        + "False and true select the left and right arms. The source has one Boolean root and two original infinite bit paths. "
                        + "The policy uses its original seed and the acquired action and reply lists; switching sides is unrestricted.")),
                    Paragraph(Text(
                        "For each chronological index k below n, actualRiseCount(p,u,z,s,n) counts k exactly when "
                        + "h = actualRun(p,u,z,k) is not stopped, the policy chooses s at h, and the original edge "
                        + "at sideCount(h.actions,s) has inner endpoint false and outer arm label true. "
                        + "Thus the count is over actual acquired edges, including the final query index when n = T. "
                        + "The final query is 00 and contributes zero to both sides.")),
                    Paragraph(Text(
                        "Here root(z) is the source's Boolean first coordinate, and subtraction and division are natural-number operations. "
                        + "The theorem quantifies both roots, every measurable seed space, every policy and seed, every source with no adjacent ones, "
                        + "and every finite first stopping time T. The preterminal arm lengths are read from zeroReplay at T minus one. "
                        + "No probability law or finite mean is assumed.")),
                    Paragraph(Text(
                        "The proof first identifies chronological rise counts with counts along each actually acquired arm prefix by induction on execution time, "
                        + "including absorbed states. The stopped_execution_replay_bridge identifies the preterminal actions with zeroReplay. "
                        + "The no_marker_iff_alternating_prefix theorem then identifies the bit prefix, and the pinned natural-number residue count gives its half-length.")),
                    Paragraph(Text(
                        "This is the finite edge-count identity used for the success exponents in the joint-parameter stopping experiment. "
                        + "It supplies no density formula, measurable archive bijection, almost-sure termination, tail estimate or parameter recovery. "
                        + "The latent endpoints occur in the mathematical count and its proof; no new observable port or continued execution after stopping is asserted."))),
                DescribeRole.Theorem))));
    }
}
