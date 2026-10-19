using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths;

internal sealed class FixedCutCoherenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence.";
    private static DocumentBlock Item(string selector, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create("fixedcut-" + selector.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete fixed-cut coherence for endpoint-preserving numbered group paths.",
        H("Complete records and reversible fixed cuts"),
        Blocks(
            Paragraph(Text("This is a reusable supplier for original sections 25.1–25.5, not a proof of that entire result. Its exact declarations are linked by owner handles. The generic statements quantify over an arbitrary universe and finite ordered group H, arbitrary dimensions and group matrices, every displayed endpoint-preserving bijection, and every legal input of the displayed dependent type. Word and At keep actual H labels, independent parallel-copy numbers and every dependent endpoint. FlatOut keeps both boundary edges, their middle vertex and the entire output word. No scalar equality or independent witness replaces equality of these records.")),
            Item("concatEquiv", "A reversible cut at a prescribed position", "Concatenation and cut are inverse on legal fibre products. The zero-length case retains its named vertex; the successor proof reconstructs all numbered edges and their endpoints. No default edge is supplied for an incompatible seam.", DescribeRole.Definition),
            Item("encoding", "The entire record is encoded with its fixed cut", "First apply psi to the original left/right boundary pair, then concatenate the full output word. The inverse recovers both cuts and every original boundary coordinate.", DescribeRole.Definition),
            Item("run_path", "The local recurrence equals the two complete sweeps", "For every word length d, local fibre-product squares return exactly the full flatDouble record. Induction exchanges independent front and back operations with the common endpoints fixed. This is not an assumption that arbitrary adjacent functions commute."),
            Item("finite_overlap", "Finite inverse overlap forces literal one-edge alignment", "Assume FlatBalanced at positive lag L and an actual diagonal continuation edge at each source vertex. Apply the inverse-block law to overlapping finite blocks, use a legal repeated right continuation and recover the common prefix and final edge. The conclusion is Aligned for the same phi, chi and psi. Both positivity of lag and continuation remain explicit hypotheses; the six laws alone are not asserted sufficient."),
            Item("full_overlap", "All-length equality of full output records", "Under the literal Aligned hypothesis, every finite d, including d=0, has flatDouble equal to fixedCutDouble on the same entire typed input. A whole-word invariant identifies the encoding before reversible decoding; this retains the output word as well as both cuts."),
            Item("full_inverse_coherence", "Both inverse identities for the complete output", "The same all-length equality gives both inverse directions on FlatInput and FlatOut. These are full dependent record identities, not just boundary or total-label identities."),
            Paragraph(Text("Admission and audit: the complete-record recurrence and overlap invariants supply the substantive content. Every retained auxiliary declaration lies on a live proof path of the complete-record recurrence or overlap results. Four-slot registration is unfinished: https://github.com/the-omega-institute/trureturing/issues/18714 records the missing compiled reconstruction, whole-family interventions, sensitivity and observational dependence. Under CLAUDE section 3.9 this linked issue discloses the unfinished audit; declared_validated is zero. Lean acceptance does not validate the missing registrations.")),
            Paragraph(Text("Remaining original25 obligations include padded partition coordinates; actual augmentation, actual Inertness and exact positive depths; arbitrary rectangular SSE, arbitrary positive SE lower bounds and full certificate counting/minima; the actual prescribed history map with signed windows for every h; and positive-j fibre counts for every h and every positive j. These fixed-cut results do not discharge those obligations.")),
            Paragraph(Text("Provenance and literature: these are repository constructions building on the existing counted-path suppliers. No external priority or literature novelty claim is made.")))));
}
