using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class TwoAxisFiniteRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/TwoAxisFiniteRotation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite generation by two full axis circles and transport with moving axes.",
        H("Two axis circles and finite rotation words"),
        Blocks(
            Paragraph(Text(
                "The vector space is the original real Euclidean three-space. "
                + "Rotations are actual linear isometric equivalences with determinant one. "
                + "The argument combines the classical reflection and sphere-connectedness "
                + "results supplied by Mathlib with an explicit intersection of two latitudes. "
                + "All products below are finite products of actual orthogonal maps.")),
            Node("axis-circle", "axisCircle", "The full circle fixing an axis",
                "For a vector a, the axis circle consists of every orthogonal map "
                + "whose determinant is one and which fixes a. The definition also "
                + "makes sense for a zero axis, although the generation theorem requires "
                + "strictly positive Gram determinant for its two axes.", DescribeRole.Definition),
            Node("finite-word", "IsAxisWord", "Allowed finite words",
                "Every letter of a finite list belongs to the full circle fixing a "
                + "or to the full circle fixing b. Multiplication is composition, "
                + "so a product R times S acts by first applying S and then R.",
                DescribeRole.Definition),
            Node("word-group", "wordGroup", "The algebraic word subgroup",
                "A map belongs to the word subgroup precisely when it equals the "
                + "product of an allowed finite list. The empty list supplies the "
                + "identity, concatenation supplies multiplication, and reversing "
                + "the list of inverse letters supplies inversion.", DescribeRole.Definition),
            Node("exact-generation", "two_axis_finite_word", "Exact generation of all rotations",
                "Let a and b be arbitrary real three-vectors whose squared inner "
                + "product is strictly less than the product of their squared norms. "
                + "Every orthogonal map R of determinant one is the product of a "
                + "finite list with every letter fixing a or b and having determinant one. "
                + "Neither axis is required to have unit norm. After normalization, "
                + "write d for their inner product and q for one minus d squared. "
                + "For every latitude t between d squared and one, an explicit unit "
                + "vector has latitude d about b and latitude t about a. Two circle "
                + "elements therefore reach an entire cap about a. This gives a "
                + "uniform metric neighborhood in its finite-word orbit. Translating "
                + "that neighborhood proves the orbit and its complement open in the "
                + "unit sphere. Connectedness makes the orbit the whole sphere. "
                + "Finally, after matching R on a, the remaining rotation fixes a "
                + "and is itself an allowed letter. The conclusion is equality with "
                + "a finite product, without any limit of words.", DescribeRole.Theorem),
            Node("pair-action", "rotatePair", "Simultaneous rotation of two inputs",
                "A rotation acts on a pair of vector inputs by applying that same "
                + "rotation to each vector. Scalar coordinates can be held fixed as "
                + "parameters of the function evaluated on the pair.", DescribeRole.Definition),
            Node("moving-axis", "moving_axis_invariance", "Fixed outputs under moving-axis transport",
                "Fix a pair p, two axes a and b with strictly positive Gram determinant, "
                + "and a function F on vector pairs with any output type. Suppose that "
                + "at every determinant-one rotated input O p, left rotation by any "
                + "map in either full circle fixing O a or O b preserves F at that "
                + "input. Then every determinant-one rotation R satisfies F(R p)=F(p). "
                + "This is equality of the same outputs; the codomain carries no "
                + "rotation action and needs no topology. To append a fixed-axis "
                + "letter g on the right of the accumulated map O, apply the local "
                + "law to O g O inverse on the left. This conjugate fixes the current "
                + "axis and takes O p exactly to (O g) p. Induction over an exact "
                + "finite word proves the stated equality. For a scalar/vector "
                + "residual this mechanism requires its actual circle laws and "
                + "transported axes, but no continuity of the residual.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
