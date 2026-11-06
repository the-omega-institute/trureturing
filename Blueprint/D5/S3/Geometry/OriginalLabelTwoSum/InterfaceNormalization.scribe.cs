// SOURCE ONLY. Every node selects a real public declaration of the owner.
// StatementSource.FromLean is resolved later from actual elaborated exports.
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class InterfaceNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DocumentHeader.Create(
            GidRef.Create("D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization"), Generality.General,
            GidRef.Create("D5/B/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization"),
            new EvidenceMirror.Waiver(WaiverReason.Create("original-label-interface-normalization")),
            [], Digest.Create("Physical interface normalization preserves actual path rows and the full right raw input; the corrected parent formula consumes the existing row transport.")),
        H("Physical interface normalization"),
        Blocks(
            Node("kappa", "kappa", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.kappa", "The physical unordered edge of an original chord index. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("physicalsurvivor", "PhysicalSurvivor", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.PhysicalSurvivor", "Original physical survivor indices, without quotienting any other fiber. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("physicalrows", "physicalRows", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.physicalRows", "Restrict exactly the index type; ground, labels and rows stay original. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("e_edge", "E_edge", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.E_edge", "The unrestricted physical-edge deletion root in the existing raw Family. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("uniqueinterface", "UniqueInterface", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.UniqueInterface", "Local U*: uniqueness only over the selected interface, never globally. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("rows_eq_of_kappa_eq", "rows_eq_of_kappa_eq", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.rows_eq_of_kappa_eq", "Equal physical chords have equal actual path-derived rows, including the reversed orientation. This follows from tree path uniqueness, not an input. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("normalizeinterface", "normalizeInterface", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalizeInterface", "Normalize only the interface fiber: retain c and every noninterface original index. Every other GraphData field is literally inherited. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("normalizedchord", "normalizedChord", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalizedChord", "The retained distinguished index is c itself, with subtype evidence. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("normalized_row", "normalized_row", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_row", "Normalization changes no row at any retained original index. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("normalized_distinguished_row", "normalized_distinguished_row", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_distinguished_row", "The interface's actual path row is preserved. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("normalized_root", "normalized_root", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_root", "The complete raw root is unchanged, including empty-face membership. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("normalized_uniqueinterface", "normalized_uniqueInterface", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_uniqueInterface", "The normalized presentation has U*, with no restriction on other fibers. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("uniqueinterface_iff_survivor_indices", "uniqueInterface_iff_survivor_indices", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.uniqueInterface_iff_survivor_indices", "U* is exactly the survivor-index identification. No necessity assertion about accidental equalities of raw face sets is made. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("e_edge_eq_without", "E_edge_eq_without", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.E_edge_eq_without", "Explicit local COROLLARY: physical deletion is one-index deletion under U*. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("normalizedsurvivorequiv", "normalizedSurvivorEquiv", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalizedSurvivorEquiv", "Canonical identity-on-original-indices equivalence after normalized deletion. In particular, duplicate noninterface indices remain distinct. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("normalized_without_root", "normalized_without_root", "D5.S3.Geometry.OriginalLabelTwoSum.GraphData.normalized_without_root", "The normalized one-index deletion is precisely E_edge on the same ground. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("physicaltransportedrows", "physicalTransportedRows", "D5.S3.Geometry.OriginalLabelTwoSum.physicalTransportedRows", "Literal corrected row presentation, indexed by old left chords and every original physical right survivor. Its right rows are original actual path rows. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("normalized_row_transport", "normalized_row_transport", "D5.S3.Geometry.OriginalLabelTwoSum.normalized_row_transport", "Both the full right input and the normalized transport output are faithful. The second equality consumes the original row_transport, with the distinguished path row preserved and the deleted-index term replaced by E_edge. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("physical_row_transport", "physical_row_transport", "D5.S3.Geometry.OriginalLabelTwoSum.physical_row_transport", "Unrestricted corrected row-algebra parent formula. There is no assumed graph/root equation here. Binding the physical presentation to the actual glued graph requires the independent G1A construction and path theorem. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("physical_row_transport_of_unique", "physical_row_transport_of_unique", "D5.S3.Geometry.OriginalLabelTwoSum.physical_row_transport_of_unique", "Local U* COROLLARY of the unrestricted formula; no global injectivity. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("next", "next", "D5.S3.Geometry.OriginalLabelTwoSum.CyclicInterface.next", "Successor around Fin m, written with an explicit wrap for arithmetic proofs. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Definition),
            Node("cyclic_edge_injective", "cyclic_edge_injective", "D5.S3.Geometry.OriginalLabelTwoSum.CyclicInterface.cyclic_edge_injective", "For every m>=3, cyclic unordered edges have unique indices. Reversed endpoint matching would force a two-cycle, excluded by m>=3. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("wheel_uniqueinterface", "wheel_uniqueInterface", "D5.S3.Geometry.OriginalLabelTwoSum.Wheel.wheel_uniqueInterface", "Actual fixed W4 local U*, proved from start/finish via cyclic edges. The general cyclic uniqueness lemma is consumed on the genuine rim endpoints. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("wheel_e_edge", "wheel_E_edge", "D5.S3.Geometry.OriginalLabelTwoSum.Wheel.wheel_E_edge", "Physical W4 deletion is the existing literal E, using the local corollary. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem),
            Node("wheel_physical_row_transport", "wheel_physical_row_transport", "D5.S3.Geometry.OriginalLabelTwoSum.Wheel.wheel_physical_row_transport", "Actual W4 indexing consumes the corrected raw formula with its existing E. This remains row algebra; no actual glued graph theorem is assumed or claimed. Source only: Lean elaboration, Scribe emit and registration remain open.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
