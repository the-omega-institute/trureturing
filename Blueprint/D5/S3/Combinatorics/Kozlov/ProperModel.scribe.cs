using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class ProperModelDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/ProperModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A proper family is a downset containing the empty face and every singleton. Its cardinalities by face size give the vectors in the equal-shift sumset.",
        H("The literal proper f-vectors and their repeated sums"),
        Blocks(
            Node("family", "Family", "Families of faces", DescribeRole.Definition,
                "A family on the ground set of size n is a finite set of subsets of Fin n, the carrier used in Spine/Complexes.lean, line 38."),
            Node("fvector-type", "FVector", "The face-size coordinate space", DescribeRole.Definition,
                "An f-vector assigns a natural number to each of the n+1 face sizes, starting at zero. See the codomain in Counting/Stats.lean, line 45."),
            Node("iscomplex", "IsComplex", "Proper downsets", DescribeRole.Definition,
                "Every subset of a face is a face. The family contains the empty face and the singleton of every ground element. See Spine/Complexes.lean, line 44."),
            Node("fentry", "fEntry", "Face counts in one degree", DescribeRole.Definition,
                "Filter the family to faces of size k and take its cardinality. In degree zero the empty face contributes one. See Spine/Complexes.lean, line 57."),
            Node("fvector", "fVector", "Face counts in all degrees", DescribeRole.Definition,
                "The coordinate indexed by k counts the faces of size k. See Counting/Stats.lean, line 45."),
            Node("snf", "SnF", "The proper f-vector set", DescribeRole.Definition,
                "Take the image of all proper downsets under the f-vector map. See Counting/Duality.lean, lines 309–314."),
            Node("sumtuple", "sumTuple", "Repeated summation", DescribeRole.Definition,
                "Sum all entries of a tuple componentwise. The indexing by Fin r permits equal summands. This is Part II's summation map at zero shifts, equation (4)."),
            Node("propersumset", "properSumset", "The literal equal-shift sumset", DescribeRole.Definition,
                "Take the image of the coordinate sum over tuples whose entries all belong to the proper f-vector set. Distinct tuples with the same total contribute one vector. See Counting/Proper.lean, line 509, at zero shifts and Part II, Theorem 41."),
            Node("top", "top", "Largest occupied degree", DescribeRole.Definition,
                "Take the largest degree having a positive count, with value minus one if all counts vanish. See Counting/Stats.lean, lines 105–108."),
            Node("indeg", "indeg", "First missing degree", DescribeRole.Definition,
                "Take the least degree whose count is below the full binomial layer. Use n+1 when no degree is deficient. See Counting/Stats.lean, lines 112–115."),
            Node("chained", "Chained", "Adjacent degree separation", DescribeRole.Definition,
                "In each adjacent pair of vectors the last occupied degree of the preceding vector is strictly below the first missing degree of its successor. This is the equal-shift case of Counting/Chaining.lean, line 361."),
            Node("top-le", "top_le", "The top lies in the face window", DescribeRole.Theorem,
                "All occupied degrees lie between zero and n. The empty support sentinel is also at most n. See Counting/Stats.lean, line 122."),
            Node("top-lt-of-vanish", "top_lt_of_vanish", "Vanishing above a threshold bounds the top", DescribeRole.Theorem,
                "If all degrees from k onward vanish, any maximum occupied degree lies below k. Empty support uses the sentinel."),
            Node("indeg-eq-sentinel-or-missing", "indeg_eq_sentinel_or_missing", "The minimum is deficient unless it is the sentinel", DescribeRole.Theorem,
                "A nonempty set of deficient degrees supplies its minimum. When the set is empty the designated value is n+1."),
            Node("layer", "layer", "A uniform layer of faces", DescribeRole.Definition,
                "This is the set of all k-element subsets of the n-element ground set."),
            Node("mem-layer", "mem_layer", "Membership in the full layer", DescribeRole.Theorem,
                "A ground-set subset belongs to the selected layer exactly when its cardinality is the degree."),
            Node("card-layer", "card_layer", "The binomial layer capacity", DescribeRole.Theorem,
                "Counting k-subsets of an n-element set gives the binomial coefficient."),
            Node("missing", "missing", "Missing faces of one size", DescribeRole.Definition,
                "Remove the faces of the family from the full layer of the selected size."),
            Node("fentry-add-card-missing", "fEntry_add_card_missing", "Present and missing faces partition a layer", DescribeRole.Theorem,
                "The filter of present k-faces and the missing k-faces are disjoint and exhaust the uniform layer."),
            Node("missing-upshadow-subset", "missing_upShadow_subset", "Missing layers are closed under upper shadows", DescribeRole.Theorem,
                "If a missing face is contained in a face one element larger, downwards closure forces the larger face to be missing."),
            Node("missing-zero", "missing_zero", "The empty face is present", DescribeRole.Theorem,
                "In degree zero the layer consists only of the empty face, which properness requires."),
            Node("missing-one", "missing_one", "Every singleton is present", DescribeRole.Theorem,
                "Every degree-one face is a singleton and belongs to a proper downset."),
            Node("frommissing", "fromMissing", "Reconstruction from missing layers", DescribeRole.Definition,
                "Keep every subset whose own cardinality layer does not mark it as missing."),
            Node("frommissing-iscomplex", "fromMissing_isComplex", "Reconstructed families are proper downsets", DescribeRole.Theorem,
                "Repeatedly add one element to propagate missing status upwards through the shadow inclusions. The vanishing missing layers in degrees zero and one supply the two properness conditions."),
            Node("missing-frommissing", "missing_fromMissing", "Recovery of the missing layer", DescribeRole.Theorem,
                "If every prescribed missing family belongs to its degree layer, reconstructing and then taking missing faces recovers it."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-proper-model-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            name is "Family" or "FVector" or "IsComplex" or "fEntry" or "fVector" or "SnF" or "sumTuple"
                or "properSumset" or "top" or "indeg" or "Chained" or "top_le"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
