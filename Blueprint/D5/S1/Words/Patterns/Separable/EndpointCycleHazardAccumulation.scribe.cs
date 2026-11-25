using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointCycleHazardAccumulationDocument : IScribeDocumentDefinition
{
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Statement()
    {
        var e = F.Id("e");
        var w = F.Id("w");
        var j = F.Id("j");
        var k = F.Id("k");
        var n = F.Id("N");
        var shifted = Seq(e, Plus, Call("streamDiscrepancy", j, w));
        var divergence = Seq(Sum, Underscore, Grp(Seq(j, InMacro, Sp, Naturals)), Sp,
            Call("nextHazard", shifted), Eq, Sp, Infty);
        var recurrence = Seq(Forall, Sp, n, InMacro, Sp, Naturals, Comma, Sp,
            Exists, Sp, k, InMacro, Sp, Naturals, Comma, Sp, n, Le, Sp, k,
            Sp, Land, Sp, w, InMacro, Sp, Call("hitAt", e, k));
        var eventSet = Seq(OpenBrace, w, InMacro, Sp, F.Id("Stream"), Mid, Sp,
            divergence, Sp, Land, Sp, Open, recurrence, Close, CloseBrace);
        var complement = Seq(eventSet, Caret, Grp(F.Id("c")));
        return Disp(Seq(Forall, Sp, e, InMacro, Sp, Integers, Comma, Quad,
            Call("streamMeasure", complement), Eq, Sp, D(0)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual hazards diverge and actual shifted hits recur on one event of full measure for each initial offset.",
        H("Hazard accumulation and recurrence for the actual cycle stream"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-hazard-accumulation-and-recurrence"),
            DeclarationHandle.Create(
                "D5/S1/Words/Patterns/Separable/EndpointCycleHazardAccumulation.actual_hazard_accumulation_and_recurrence"),
            H("Infinite total hazard and arbitrarily late shifted hits"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The integer e is the initial discrepancy. The stream sample w is distributed by the actual mark law. "
                    + "At index j, the incoming discrepancy is e plus the discrepancy of the j completed marks. "
                    + "The event hitAt(e,k) tests the actual mark k at this incoming discrepancy, before adding its own advance.")),
                Paragraph(Text(
                    "The uniform quadratic marginal bound gives divergence of the sum of the logarithmic discrepancy profile. "
                    + "The raw occupation lower envelope bounds the first term of the exact nonnegative hazard series. "
                    + "A positive multiple of the divergent profile sum is therefore no greater than the total actual hazard. "
                    + "The strict-past conditional recurrence theorem then gives hits beyond every threshold on the same "
                    + "full-measure event, without any independence assumption on the hit events."))),
            DescribeRole.Theorem))));
}
