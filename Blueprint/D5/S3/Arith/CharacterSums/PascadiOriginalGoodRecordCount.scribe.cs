using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalGoodRecordCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual bounded good records count the original integer parameters and endpoint incidences without an extra parameter lift.",
        H("Actual good-record incidence"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-actual-bounded-good-record-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordCount.actual_bounded_good_record_count"),
                H("Count bounded actual good incidences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0 there is one C>0 valid for all primes p, widths 0<X<=Y with 3Y<p^2, coordinate bounds J1,J2>=1, fixed alternating units a1,a2 modulo p^3, and finite sets T of actual triples (wt,base,e). Each triple must be a GoodRecordRealization in its selected actual reduced physical basis: the basis is long, its first horizontal coordinate and the original middle t are units, both endpoints satisfy the original six-word equation, both first-coordinate entries of the baseline are units, and the partner pencil has nonzero derivative at the actual physical slope modulo p. The anchor identity is physical(R,V,q(wt))=-wt. Bound the anchor and four endpoint coordinate vectors by J1,J2. Then card(T)<=C p^epsilon (9J1J2)^5.")),
                    Paragraph(Text("Map an incidence to its anchor and four endpoint coordinate vectors. For a fixed record, map actual incidences to their physical bases. Equal bases and equal anchor coordinates recover the same original integer wt through the physical anchor identity; equal records then recover both endpoint pairs. This proves the needed injection, rather than assuming it. The existing actual_good_record_realizations_subpower bounds each record fiber by C p^epsilon.")),
                    Paragraph(Text("Each of the five coordinate vectors belongs to a literal symmetric integer rectangle. For J>=1 the interval [-floor(J),floor(J)] has at most 3J integers, so each coordinate rectangle has at most 9J1J2 members. Count their fivefold product, then sum the proven realization bound over actual record fibers. There is no independent choice of a slope lift, original parameter, or complementary basis vector."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is the bounded incidence ingredient for the retained-chart second moment. The derivative-zero partners, the summation over physical scales, removed unit-chart pieces, and the final original six-tuple conjecture still require their own estimates. A good-record count by itself does not prove that conjecture.")))));
}
