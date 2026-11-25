using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedContactCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed contact cancellation in the nine-cube",
        H("The separated cubic supports"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia's Problem 2 asks whether the nine-cube has a 258-point induced support of maximum degree three. Consider the candidate consisting of two separated components. https://arxiv.org/html/2610.09483v1#Thmproblem2 Take disjoint connected Huang-balanced cubic induced supports C and D of sizes 72 and 186 with no cube edge between them. Fix a cube parity b. Let f and g be their switching vectors extended by zero and restricted to b. For axes i and j, write A(x) for f(x) times the signed double flip of g by ΓᵢΓⱼ at x.")),
            Describe.Lean(
                DescribeId.Create("q9-signed-contact-parity"),
                DeclarationHandle.Create(Prefix + "signed_overlap_parity_zero"),
                H("Signed contacts cancel on each parity"),
                StatementSource.FromAuthor(Disp(Seq(Sum, Underscore, Grp(F.Id("x")), Sp,
                    F.Id("A"), Open, F.Id("x"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Give axis j weight t and every other axis weight one. The resulting Huang operator squares to (8 + t²)I. The crossing map sends the 129 selected vertices on parity b to the 127 exterior vertices on the opposite parity. On its kernel, the C and D images are orthogonal. Their interior supports are disjoint by separation and their exterior images are negatives of each other. The sum of exterior squares therefore vanishes and each image stays on its own support.")),
                    Paragraph(Text("Pair the D part with Γᵢ applied to the fixed C switch f. The weighted image stays on D, so separation makes the pairing zero. At unit weights the anticommutator and the switching eigen-equation also make it zero. Their difference is t − 1 times the signed overlap functional L, which consequently vanishes on the crossing kernel for t ≠ 1.")),
                    Paragraph(Text("Append evaluation at one C vertex of parity b and the row L. Rank-nullity leaves a nonzero zero-vector for these rows and the crossing whenever t ≠ 1. The augmented matrix has order 129 and its determinant is continuous, so it is singular at t = 1. Each component part at unit weights lifts to a supported eigenvector of eigenvalue 3 by adding one third of its Huang image. The edge identity and connectedness make that eigenvector a multiple of the component switch. The root evaluation kills the C multiple, leaving a nonzero D multiple on which L vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-signed-contact-cell"),
                DeclarationHandle.Create(Prefix + "signed_overlap_cell_zero"),
                H("For distinct axes, signed contacts cancel in every two-bit cell"),
                StatementSource.FromAuthor(Disp(Seq(Sum, Underscore,
                    Grp(F.Id("x"), Sp, Colon, Sp, F.Id("x"), Underscore, F.Id("i"), Eq, F.Id("p"),
                        Comma, Sp, F.Id("x"), Underscore, F.Id("j"), Eq, F.Id("q")), Sp,
                    F.Id("A"), Open, F.Id("x"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For distinct i and j, multiply the C switch by either bit character or by their product. Conjugation negates the weights on the character's axes and preserves the supported eigen-equation. The weighted anticommutator on C and separation on D then give the vanishing overlap against each nonconstant character. Probe with an axis whose other axis has changed sign. A diagonal term vanishes by disjointness because Γᵢ² = I.")),
                    Paragraph(Text("The parity result supplies the constant coefficient. The indicator of a fixed pair of bits p and q is one quarter of the product of the two corresponding character factors, so its expansion uses precisely these four zero coefficients."))),
                DescribeRole.Theorem)),
        []));
}
