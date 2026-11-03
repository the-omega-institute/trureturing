using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class LeechMinimalCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/LeechMinimalCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/nebe2014leechcatalogue");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete integer minimum sphere",
        H("The complete integer minimum sphere"),
        Blocks(
            Paragraph(Text("The sphere contains all integer-valued functions on Fin 24 satisfying the original Golay congruences and square sum 32; its domain is unbounded. Even vectors have either two coordinates of absolute value four, or a Golay octad of coordinates of absolute value two with even minus-sign parity. Odd vectors have one coordinate of absolute value three and twenty-three unit coordinates, determined by a distinguished position and an actual Golay codeword. The family sizes are 1104, 97152 and 98304. The rational function scaledSquare is squareSum divided by eight. This coordinate classification supplies no real self-duality, unimodular Gram realization, uniqueness theorem, VOA dimension, Monster representation or string-theory construction.")),
            Node("leechminimalcount-familyvector-surjective-on-sphere", "familyVector_surjective_on_sphere", "Every unbounded sphere vector has a family",
                "Every element x of the actual admissible integer square-sum-32 sphere is familyVector p for some p in the disjoint union of the two-support, even-signed-octad and distinguished-position codeword families. The congruence representation determines parity; the square-sum bound and code minimum force each possible coordinate shape. No coordinate box or classification premise is imposed.", DescribeRole.Theorem, false),
            Node("leechminimalcount-sphereequiv", "sphereEquiv", "A bijection with the three families",
                "The complete disjoint family type is equivalent to the subtype of admissible integer vectors with square sum 32. Every constructed vector satisfies the congruences and square sum. The support, quotient residue, exceptional odd coordinate and sign parity distinguish the families and recover their parameters.", DescribeRole.Definition, false),
            Node("leechminimalcount-shortest-vectors-finite", "shortest_vectors_finite", "Actual finiteness of the sphere",
                "The full subtype of admissible functions Fin 24 to the integers with square sum 32 is finite, by equivalence with the three finite parameter families. Finiteness is derived on the original unbounded domain.", DescribeRole.Theorem, false),
            Node("leechminimalcount-shortest-vectors-card", "shortest_vectors_card", "The classical count 196560",
                "The cardinality of all admissible integer vectors of square sum 32 is 196560. The counts are binomial(24,2) times four for the two-support family, 759 times 128 for the signed octads, and 24 times 4096 for the odd family. The code cardinality and octad count are proved properties of the original encoder image, not new premises.", DescribeRole.Theorem, true),
            Node("leechminimalcount-scaled-shortest-vectors-finite-card", "scaled_shortest_vectors_finite_card", "The literal rational squared-length-four sphere",
                "The subtype of admissible integer vectors with scaledSquare equal to four is finite and has cardinality 196560. Here scaledSquare is exactly squareSum divided by eight in the rationals. The identity map on vectors is a two-sided equivalence with square sum 32. No real lattice or operator-state realization is assumed or supplied.", DescribeRole.Theorem, true))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role, bool attested) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(),
            attested ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
