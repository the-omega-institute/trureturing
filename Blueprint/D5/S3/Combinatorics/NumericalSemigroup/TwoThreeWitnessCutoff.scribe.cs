using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NumericalSemigroup;

internal sealed class TwoThreeWitnessCutoffDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Combinatorics/NumericalSemigroup/TwoThreeWitnessCutoff.best_two_witness_cutoff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum cutoff over two-witness spans for the degree row (2, 3).",
        H("Optimal two-witness cutoff for the row (2, 3)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("best-two-witness-cutoff"),
                DeclarationHandle.Create(Result),
                H("Eight is the smallest cutoff over the witness choices"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The degree of an integer vector x is 2x₁ + 3x₂. An eligible "
                        + "integer cutoff C admits one strictly positive integer vector p and one "
                        + "signed integer vector u of degree 1 such that every integer t ≥ C is "
                        + "the degree of a nonnegative vector in their integer span. Viable(p,u,t) denotes this last condition.")),
                    Paragraph(Text("For a cutoff at most seven, choose vectors of degrees 7, 8, "
                        + "9 and 10 in the same span. The absolute determinant of the witnesses "
                        + "is at least two since the entries of u have opposite signs. It divides "
                        + "the determinant of every pair of vectors in the span. The nonnegative "
                        + "solutions at the four degrees force the determinant to have absolute "
                        + "value two. This forces u = (−1, 1). The unique vector (2, 1) of "
                        + "degree 7 has determinant 3 with that u, giving a contradiction.")),
                    Paragraph(Text("With p = (1, 1) and u = (−1, 1), write t = 8 + 4q + r "
                        + "with q ≥ 0 and 0 ≤ r < 4. The vector (4 + 2q − r, r) has degree t "
                        + "and is an integer combination of the two witnesses. Thus eight "
                        + "is attained."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula c = F.Id("C");
        Formula p = F.Id("p");
        Formula u = F.Id("u");
        Formula t = F.Id("t");
        Formula z = new Formula.Integers();
        Formula cutoffs = Seq(OpenBrace, c, Sp, InMacro, Sp, z, Sp, Mid, Sp,
            Exists, Sp, p, Comma, u, Sp, InMacro, Sp, z, Caret, D(2), Comma, Sp,
            new Formula.Subscript(p, D(1)), Sp, Gt, Sp, D(0), Sp, Land, Sp,
            new Formula.Subscript(p, D(2)), Sp, Gt, Sp, D(0), Sp, Land, Sp,
            Call("degree", u), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Open, Forall, Sp, t, Sp, InMacro, Sp, z, Comma, Sp, t, Sp, Geq, Sp, c,
            Sp, Rightarrow, Sp, Call("Viable", p, u, t), Close, CloseBrace);
        return Disp(Seq(Call("min", cutoffs), Sp, Eq, Sp, D(8)));
    }
}
