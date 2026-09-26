using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class FinitePhaseMixtureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small off-diagonal mass admits an exact finite phase mixture.",
        H("Finite Phase Mixtures"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-phase-mixture"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/FinitePhaseMixture.result"),
            H("Representation by unit-coordinate outer products"),
            StatementSource.FromAuthor(Representation()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let d be any positive natural number and H any complex Hermitian d by d matrix. Assume every diagonal entry is one and the sum of the norms of H(i,j) over i < j is at most one. There is a positive natural number n, nonnegative real weights indexed by Fin n summing to one, and complex vectors whose every coordinate has norm one, with the displayed exact representation for every i and j. No positive-semidefinite hypothesis is required.")),
                Paragraph(Text("Uniform independent signs have zero mixed moments at distinct coordinates. For an ordered pair i < j, identify its two sign coordinates and multiply coordinate j by conjugate(H(i,j))/norm(H(i,j)). This leaves only the chosen pair and its conjugate as off-diagonal moments. A zero entry uses phase one and receives weight zero. Mix these pair distributions with weights norm(H(i,j)); the identity sign distribution receives the remaining mass.")),
                Paragraph(Text("The construction uses (1+d squared) times 2 to the d labelled terms, allowing repetitions and zero weights. The index is nonempty even when all pair weights vanish. There is no division by the off-diagonal mass or by its remainder, so dimensions one and two and total masses zero and one are included."))),
            DescribeRole.Theorem))));

    private static Formula Representation()
    {
        Formula p = Seq(F.Id("p"), Underscore, Grp(F.Id("a")));
        Formula zi = Seq(F.Id("z"), Underscore, Grp(F.Id("a"), F.Id("i")));
        Formula zj = Seq(F.Id("z"), Underscore, Grp(F.Id("a"), F.Id("j")));
        return Disp(Seq(
            Forall, Sp, F.Id("i"), Comma, F.Id("j"), Comma, Sp,
            F.Id("H"), Underscore, Grp(F.Id("i"), F.Id("j")), Eq,
            Sum, Underscore, Grp(F.Id("a"), Eq, D(1)), Caret, Grp(F.Id("n")),
            p, zi, Overline, Grp(zj), Comma, Sp,
            p, Ge, D(0), Comma, Sp,
            Sum, Underscore, Grp(F.Id("a"), Eq, D(1)), Caret, Grp(F.Id("n")), p, Eq, D(1),
            Comma, Sp, Vert, Sp, zi, Vert, Eq, D(1), Comma, Sp, F.Id("n"), Gt, D(0)));
    }
}
