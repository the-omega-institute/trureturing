using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class TripleMatrixRecordsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/TripleMatrixRecords.";
    private static readonly LibraryNoteRef Note =
        LibraryNoteRef.Create("D5/L/QuantumStates/barnumhilgert2019spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace-preserving PSD order coordinates give first-pair discard and all six label permutations on the actual triple.",
        H("Coherent coordinates, discard and record relabeling"),
        Blocks(
            Law("all-vector-coordinates", "CoherentCoordinates", "Coordinates on the fixed pair and triple",
                "The singleton coordinates are the identity. The pair and triple equivalences preserve trace and preserve PSD in both directions. In (30) they identify the given M with the tensor product and the given L(q,z) with the tensor of the coordinated q and z for every Hermitian pair vector q and every singleton z, including entangled pair inputs.",
                DescribeRole.Definition),
            Law("coordinates-from-two-pairs", "coherentCoordinates", "Construct the coordinates from the two actual pair readbacks",
                "The two whole-PSD pair readbacks, both real spans and both exact unitary tensor forms give the coordinates. The scalar case n = 1 uses trivial transposition. The normalized forms are the explicit external proof inputs attributed to Xu, Zheng and Fošner, Main Theorem (1.1)–(1.2) and the one-factor Proposition 2.1. Equation numbers outside that citation refer to the Barnum–Hilgert Library note. https://doi.org/10.1017/S1446788714000603",
                DescribeRole.Definition),
            Law("discard-positive", "marginal12_psd", "First-pair discard is positive on the entire actual triple",
                "Transport the ordinary partial trace through the actual triple and pair equivalences.",
                DescribeRole.Theorem),
            Law("discard-trace", "marginal12_tp", "First-pair discard preserves the canonical trace",
                "The two coordinate changes and the partial trace preserve the trace.",
                DescribeRole.Theorem),
            Law("discard-readback", "marginal12_read", "Read back the whole first pair",
                "On the given L(q,z), the constructed map returns tr(z) times q for all q and z.",
                DescribeRole.Theorem),
            Law("discard-unique", "marginal12_unique", "Spanning makes the first-pair discard unique",
                "Every real-linear map with this all-vector law equals the constructed map by Spans L. This identifies any p12 supplied in TripleMarginals through coherentCoordinatesOfTriple_marginal12.",
                DescribeRole.Theorem),
            Law("relabeling-action", "recordRelabel_prep", "Permute the actual preparation labels",
                "Each of the six permutations σ of Fin 3 acts on the fixed triple. In target slot i the output preparation uses input f(σ i). At n = 1 every label permutation acts trivially.",
                DescribeRole.Theorem),
            Law("relabeling-positive", "recordRelabel_psd", "Each relabeling preserves PSD in both directions",
                "The map is the ordinary factor permutation conjugated by the triple coordinate equivalence.",
                DescribeRole.Theorem),
            Law("relabeling-trace", "recordRelabel_tp", "Each relabeling preserves trace",
                "Reindexing rows and columns by the same permutation preserves the diagonal sum in coherent coordinates.",
                DescribeRole.Theorem),
            Law("faithful-relabeling", "recordRelabel_faithful", "Distinct permutations give distinct maps in an active sector",
                "When n is at least two, diagonal Hermitian matrices distinguish coordinate permutations, and two singleton coordinates suffice to detect each slot label. Thus the action is faithful as well as positive and trace preserving.",
                DescribeRole.Theorem),
            Law("relabeling-composition", "recordRelabel_comp", "The relabelings compose on the whole triple",
                "With the target-slot convention, applying σ and then τ gives the label map i ↦ σ(τ(i)). The two spans extend composition on actual nested preparations to every triple vector.",
                DescribeRole.Theorem),
            Law("supplied-first-pair", "coherentCoordinatesOfTriple_marginal12", "Identify the supplied first-pair marginal",
                "Instantiating the construction with the actual TripleMarginals data identifies its supplied p12 by the all-vector readback and Spans L.",
                DescribeRole.Theorem),
            Law("relabeling-marginals", "retained_eq_marginal12_relabel", "Identify the actual retained-pair readbacks",
                "The all-vector preparation law and the two spans identify each retained-pair map with the corresponding relabeling followed by first-pair discard.",
                DescribeRole.Theorem),
            Law("retained-pair-positive-trace", "retained_pair_psd_tp", "The retained readback is positive and trace preserving",
                "In coherent coordinates the retained readback law determines both properties on the whole actual triple, by the positive trace-preserving relabeling and the first-pair discard.",
                DescribeRole.Theorem))));

    private static DocumentBlock Law(string id, string selector, string title, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Note),
            Blocks(Paragraph(Text(explanation))), role);
}
