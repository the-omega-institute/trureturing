using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class QuadraticResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/QuadraticResidues",
            "Squares occupy only residues zero and one modulo four, obstructing residue three."),
        H("Quadratic Residues Modulo Four"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("square-residues-and-sum-obstruction"),
                H("Square residues and the two-square obstruction"),
                LeanTheorem(
                    "D5/S3/PrimeForms/QuadraticResidues."
                    + "square_residues_and_sum_obstruction"),
                LatexStatement.Create(
                    @"$$\left(\forall n\in\mathbb{N},\ n^2\operatorname{mod}4\in\{0,1\}\right)"
                    + @"\ \land\ "
                    + @"\left(\forall a,b\in\mathbb{N},\ (a^2+b^2)\operatorname{mod}4\neq3\right).$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Every natural square has residue zero or one modulo four. Consequently, "
                        + "the sum of two natural squares cannot have residue three modulo four.")),
                    Paragraph(Text(
                        "Methodologically, the zeroth-layer refutation certificate is the R_4 "
                        + "reading: inspect the square image {0, 1}, then its pairwise-sum image "
                        + "{0, 1, 2}. This certificate explains the proof search but is not an "
                        + "additional clause of the formal theorem.")))
            ))));
}
