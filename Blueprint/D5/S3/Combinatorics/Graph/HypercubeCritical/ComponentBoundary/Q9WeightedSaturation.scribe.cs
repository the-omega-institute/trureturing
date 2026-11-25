using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9WeightedSaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal weighted Gram singularity in the nine-cube",
        H("The separated cubic branch"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia's Problem 2 asks whether Q9 contains an induced support of 258 vertices with maximum degree three. The theorem below constrains the branch with two separated Huang-balanced cubic supports. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("q9-separated-cubic-weighted-gram-singular"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/"
                    + "Q9WeightedSaturation.separated_cubic_weighted_gram_singular"),
                H("The full Gram defect of C is singular at every real weighting"),
                StatementSource.FromAuthor(Disp(Seq(
                    new Formula.FunctionCall(FormulaIdentifier.Create("det"),
                        [Seq(F.Id("q"), F.Id("I"), Sp, Minus, Sp,
                            F.Id("M"), F.Id("M"), Caret, Grp(F.Id("T")))]),
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let C and D be disjoint induced cubic supports in Q9 with 258 vertices in total and no cube edge between them. Assume both are Huang-balanced and D is connected. For either parity b and arbitrary real coordinate weights w, let M be the unsigned weighted biadjacency of C, with all its parity-b vertices as rows and all its opposite-parity vertices as columns. An edge along axis i has entry wᵢ and every nonedge has entry zero. Let q be the sum of the nine squared weights and I the identity on the row space.")),
                    Paragraph(Text("Cubic regularity gives 129 vertices of each parity in the union. Delete one row of D on parity b. The switched exterior matrix then has 128 rows and 127 columns. Its Gram matrix is block diagonal, with the full defect of C and the rooted defect of D as blocks. Its rank is at most 127, so the product of the block determinants vanishes over the real polynomial ring in the nine weights.")),
                    Paragraph(Text("At unit weights the signed map from the full parity side of D to its own opposite-parity exterior has a kernel spanned by the parity restriction of its switching vector. Connectedness gives this simplicity, and the switching vector is nonzero at the deleted vertex. The rooted defect of D therefore has nonzero determinant at unit weights. Its determinant polynomial is nonzero, so cancellation in the polynomial ring makes the full determinant of C identically zero. Evaluation then gives the identity at every real weight vector, including zero or negative weights.")),
                    Paragraph(Text("For a proposed C, any integer weight vector with a nonzero exact determinant falsifies the existence of a separated connected balanced cubic partner of the required size. An external exact-integer computation used weights (1, 2, 3, 4, 5, 6, 7, 8, 9) to exclude all 32 enumerated 90-vertex lifts in the regular 12+3 case from pairing with such a 168-vertex partner. Separate external reductions and finite replays exclude the remaining cases of the 90+168 branch. The Lean theorem supplies the universal obstruction used in the determinant test."))),
                DescribeRole.Theorem)),
        []));
}
