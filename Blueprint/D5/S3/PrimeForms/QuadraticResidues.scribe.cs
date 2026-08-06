using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                Disp(Seq(Left, Open, Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("n"), Caret, D(2), Operatorname, Grp(F.Id("mod")), D(4), InMacro, OpenBrace, D(0), Comma, D(1), CloseBrace, Right, Close, Esc, Land, Esc, Left, Open, Forall, Sp, F.Id("a"), Comma, F.Id("b"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Open, F.Id("a"), Caret, D(2), Plus, F.Id("b"), Caret, D(2), Close, Operatorname, Grp(F.Id("mod")), D(4), Neq, D(3), Right, Close, Dot)),
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
            )),
[
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/PrimeForms/QuadraticResidues.square_residues_and_sum_obstruction")),
                ]));
}
