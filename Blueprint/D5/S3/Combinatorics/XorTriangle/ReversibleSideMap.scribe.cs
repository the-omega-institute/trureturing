using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.XorTriangle;

internal sealed class ReversibleSideMapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/XorTriangle/ReversibleSideMap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/bogdanov2020xortriangle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The clockwise right-edge map of a finite binary XOR triangle has third iterate equal to the identity. At each width it is a permutation whose inverse is two clockwise turns.",
        H("Three Turns of a Binary XOR Triangle"),
        Blocks(
            Paragraph(Text(
                "Start with a finite list of Boolean bits. Replace each adjacent pair by its XOR until one bit remains. The right edge is read from the upper-right corner to the apex, with every position retained. The construction is exactly rightEdge from the binary value-one classification, so leading zero bits and the empty row retain their original treatment.")),
            Describe.Lean(DescribeId.Create("xortriangle-right-edge-cube"),
                DeclarationHandle.Create(Prefix + "rightEdge_cube"),
                H("Three turns recover the row"),
                StatementSource.FromAuthor(CubeFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite Boolean row, applying rightEdge three times returns that same row. There is no restriction on length or on the first bit. The empty row is included. For a nonempty row of width n plus one, write a cell using nonnegative coordinates a, b and c with a plus b plus c equal to n. One clockwise change of side cyclically permutes these coordinates. The local XOR relation is preserved because any one of its three bits is the XOR of the other two. Three cyclic permutations recover every original cell. The proof identifies these coordinates with the actual adjacent-XOR list construction before applying the rotation identity. The argument is adapted from Ilya Bogdanov's MathOverflow answer 359278, revision 5, under CC BY-SA 4.0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xortriangle-right-edge-equivalence"),
                DeclarationHandle.Create(Prefix + "rightEdgeEquiv"),
                H("A permutation at each fixed width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural width n, rightEdgeEquiv is an equivalence from Boolean rows of length n to themselves. Its forward function is rightEdge and its inverse applies rightEdge twice. Both compositions are the three-turn identity. Retaining the width is essential: decoding the boundary as a natural number can discard leading zeros. The equivalence gives exact boundary reconstruction for arbitrary rows, beyond the special value-one case. The dimension and proper fixed-vector counting results in Bogdanov's answer require further arguments and are separate statements."))),
                DescribeRole.Definition)),
        []));

    private static Formula CubeFormula()
    {
        Formula row = F.Id("row");
        Formula word = new Formula.Apply(Named("List"), [Named("Bool")]);
        Formula edge(Formula x) => new Formula.Apply(Named("rightEdge"), [x]);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("row"), word,
            new Formula.Relation(edge(edge(edge(row))), FormulaRelationOperator.Equal, row)));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
