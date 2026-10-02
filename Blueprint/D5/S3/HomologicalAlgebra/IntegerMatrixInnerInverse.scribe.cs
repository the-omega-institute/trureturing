using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class IntegerMatrixInnerInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse.";

    private static readonly LibraryNoteRef MinorSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/fampalee2018sparse");

    private static readonly LibraryNoteRef SplittingSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/sontag1980generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A maximal nonzero minor of a finite totally unimodular integer matrix "
            + "reconstructs the whole matrix and gives an integer inner inverse.",
        H("Integer Inner Inverses from Unit Minors"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-integer-inner-inverse"),
            DeclarationHandle.Create(Prefix + "exists_integer_inner_inverse"),
            H("Every finite TU integer matrix has an integer inner inverse"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(MinorSource, SplittingSource),
            Blocks(
                Paragraph(Text(
                    "Choose a maximal nonzero square minor. The empty minor has "
                        + "determinant one, and injective row selection bounds its size, "
                        + "so this choice also covers the zero matrix. Total unimodularity "
                        + "makes the chosen determinant plus or minus one, and the minor "
                        + "therefore has an inverse over the integers.")),
                Paragraph(Text(
                    "Bordering the minor by any remaining row and column gives a "
                        + "larger minor whose determinant vanishes by maximality. The "
                        + "Schur determinant identity then forces every residual entry "
                        + "to vanish. Place the selected inverse in a transposed zero "
                        + "block matrix and transport it back to the original coordinates.")),
                Paragraph(Text(
                    "The row and column types may be empty, and the matrix may be "
                        + "rectangular or rank deficient. No nonzero-entry or full-rank "
                        + "hypothesis is needed. The conclusion is only ABA equals A: "
                        + "it asserts neither Moore–Penrose conditions nor norm optimality.")),
                Paragraph(Text(
                    "Fampa and Lee supply the real selected-minor construction; "
                        + "Sontag supplies the splitting and maximal-minor-ideal context. "
                        + "The integral TU result combines unit determinants with "
                        + "bordered-minor reconstruction and carries no originality claim."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula ResultFormula()
    {
        Formula rows = F.Id("m"), cols = F.Id("n"), matrix = F.Id("A"), inverse = F.Id("B");
        Formula integers = F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
        return F.Disp(F.Seq(
            F.Forall, F.Sp, rows, F.Comma, F.Sp, cols, F.Colon, F.Sp, F.Id("Type"), F.Comma, F.Sp,
            F.OpenBracket, Call("Fintype", rows), F.CloseBracket, F.Comma, F.Sp,
            F.OpenBracket, Call("Fintype", cols), F.CloseBracket, F.Comma, F.Sp,
            F.Forall, F.Sp, matrix, F.Colon, F.Sp, Call("Matrix", rows, cols, integers), F.Comma, F.Sp,
            Call("IsTotallyUnimodular", matrix), F.Sp, F.Rightarrow, F.Sp,
            F.Exists, F.Sp, inverse, F.Colon, F.Sp, Call("Matrix", cols, rows, integers), F.Comma, F.Sp,
            matrix, F.Sp, inverse, F.Sp, matrix, F.Sp, F.Eq, F.Sp, matrix));
    }
}
