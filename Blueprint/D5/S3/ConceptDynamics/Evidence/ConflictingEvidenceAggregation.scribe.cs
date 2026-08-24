using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Evidence;

internal sealed class ConflictingEvidenceAggregationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Evidence/ConflictingEvidenceAggregation."
            + "negative_evidence_moves_true_only_to_both";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative support joins true-only evidence into a both-supported conflict state.",
        H("Conflicting Evidence Aggregation"),
        Blocks(Describe.Lean(
            DescribeId.Create("negative-evidence-moves-true-only-support-to-both"),
            DeclarationHandle.Create(Declaration),
            H("Negative evidence moves true-only support to both"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An evidence value is the source pair of positive and negative support "
                        + "bits. Aggregation applies Boolean disjunction in each coordinate, so "
                        + "support recorded by either source is retained.")),
                Paragraph(Text(
                    "Start from the canonical true-only value and add any source whose negative "
                        + "support bit is set. The aggregate is the canonical both-supported "
                        + "value, lies above both inputs in the componentwise information order, "
                        + "and is strictly above the true-only input.")),
                Paragraph(Text(
                    "True-only evidence is consistent because one polarity is absent. The "
                        + "aggregate has both support bits, so it is inconsistent precisely by "
                        + "exposing the two sources' conflict, not by discarding information."))),
            DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("e");
        Formula trueOnly = Seq(Mathbf, Grp(F.Id("T")));
        Formula both = Seq(Mathbf, Grp(F.Id("B")));
        Formula negativeBit = Sub(source, F.Id("neg"));
        Formula aggregated = Call("aggregateEvidence", trueOnly, source);
        Formula sourceType = Seq(Operatorname, Grp(F.Id("EvidenceValue")));
        Formula informationLeFirst = Call("InformationLe", trueOnly, aggregated);
        Formula informationLeSecond = Call("InformationLe", source, aggregated);
        Formula trueConsistent = Call("EvidenceConsistent", trueOnly);
        Formula aggregateConsistent = Call("EvidenceConsistent", aggregated);

        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, sourceType, Comma, Sp,
            negativeBit, Sp, Eq, Sp, F.Id("true"), Sp, Rightarrow, RowBreak, Grp(),
            Open, aggregated, Sp, Eq, Sp, both, Close, Sp, Land, RowBreak, Grp(),
            Open, informationLeFirst, Sp, Land, Sp,
            informationLeSecond, Sp, Land, Sp,
            trueOnly, Sp, Neq, Sp, aggregated, Close, Sp, Land, RowBreak, Grp(),
            Open, trueConsistent, Sp, Land, Sp,
            Neg, Sp, aggregateConsistent, Close, Sp, Land, RowBreak, Grp(),
            Open, Sub(aggregated, F.Id("pos")), Sp, Eq, Sp, F.Id("true"), Sp,
            Land, Sp, Sub(aggregated, F.Id("neg")), Sp, Eq, Sp,
            F.Id("true"), Close, Dot));
    }

}
