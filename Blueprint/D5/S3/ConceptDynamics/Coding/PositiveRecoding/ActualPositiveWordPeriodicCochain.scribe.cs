using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class ActualPositiveWordPeriodicCochainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-history charts, endpoint-corrected positive-word gyration and signed time translation.",
        H("Actual-history charts, endpoint-corrected positive-word gyration and signed time translation"),
        Blocks(
            Paragraph(Text("These source-bound statements use the forward shift on original signed histories. The finite chart is a coordinate system for those histories and their primitive orbits, not a replacement native action. All integer times remain quantified in ht. All nonzero natural periods are retained here, and localization later restricts only to periods divisible by three.")),
            Paragraph(Text("A supplied full graph chart r writes a time-equivariant history map by composing r.homeomorph inverse, the map, and r.homeomorph. Comparison with the fixed chart is conjugation by chartComparison r. Cancellation of the two full chart equivalences and TimedEquiv.gyration_conjugate gives the same loop value. For composition, cancel the intermediate fixed chart and apply TimedEquiv.gyration_comp. These are local applications of the retained general laws to the same history maps.")),
            Describe.Lean(
                DescribeId.Create("actualpositivewordperiodiccochain-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.chart"),
                H("The existing full outgoing chart"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary finite Presentation F, matrix F is OutSplitNumberedRecoding.R F.graph id multiplied by its S factor. Its rank is the cardinality of the actual vertex type. chart F is exactly outOld F F id, retaining vertex and parallel-edge identities. primitiveChart transports true forward minimal period and orbitChart transports the existing forward-rotation quotient. The orbit Fintype instance remains. The cochain construction uses these primitive and orbit charts; fixed-period finiteness in the preserved original application belongs to that application."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualpositivewordperiodiccochain-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.positive_gyration"),
                H("Both chart corrections of a rectangular positive letter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let F and H be the literal endpoint presentations, R a natural counted matrix of size n by m, S of size m by n, old a full graph relabel from counted R*S to F.graph, and next one from counted S*R to H.graph. For any d with NeZero d, wordMap of this positive letter is the composition of chartComparison old inverse, the actual elementary R,S map, and chartComparison next. Its gyration is negative old-chart gyration plus relativeForwardGyration R S plus next-chart gyration. Neither comparison is assumed to vanish. n and m may be zero; no inverse of R, S or a time map is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualpositivewordperiodiccochain-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.word_gyration"),
                H("Composition gives the same endpoint-typed cochain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cochain is defined recursively on the actual Word F H. A relabel leaf contributes relabelMap gyration; a positive leaf contributes the three terms of positive_gyration; composition adds values. wordMap_comp proves the endpoint-chart cancellation on histories before TimedEquiv.gyration_comp is used. Induction gives wordMap gyration equals cochain for every Word and every nonzero d. There is no arbitrary-homeomorphism leaf, no inverse-recoding leaf, and no replacement by a word in residues."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualpositivewordperiodiccochain-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.time_corrected_word"),
                H("Signed time acts by the actual primitive-orbit count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a loop w : Word F F, integer s, history equivalence h, time commutation ht at every integer t and actual history x, and hh asserting h x = time F.graph s (w.eval x) for every x, historyGyration h ht d equals cochain d w plus card(Orbit F d) times s in ZMod d. This is a consequence of the actual factorization hh, not of the number of positive letters. inCharts conjugates the full history action into the same fixed chart at both ends; the time-equivariance identities and TimedEquiv.gyration_time determine the sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualpositivewordperiodiccochain-5"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualPositiveWordPeriodicCochain.historyGyration_congr_on_primitive"),
                H("Primitive agreement of actual history maps suffices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any two history equivalences h and k commuting with every integer time, agreement on every Primitive F d gives equality of historyGyration at d. The proof transfers that agreement through the same primitiveChart and uses TimedEquiv.gyration_congr. The preserved original application applies this at three and six: a true period-three history is fixed by the forward shift to the sixth power, so agreement on the literal Fix(T^6) domain controls both terms of the same character."))),
                DescribeRole.Theorem),
            Paragraph(Text("The periodic transport uses actual primitive histories and the existing orbit representatives. Composition and conjugacy laws refer to the same time-equivariant maps; they do not erase endpoint phases of an open edge.")))));
}
