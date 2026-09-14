using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GramUnitaryExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal complex column Gram matrices admit a unitary taking one rectangular matrix to the other.",
        H("Equal Gram Unitary Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-gram-unitary"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq"),
            H("One unitary on the whole common codomain"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qiclean2026gramunitary")),
            Blocks(Paragraph(Text(
                "Let m and n be finite types, and A and B complex m-by-n matrices. If their " +
                "column Gram matrices A* A and B* B agree, with star denoting conjugate transpose, " +
                "there is a unitary U on the full m-dimensional codomain such that B=UA. " +
                "Gram equality identifies all linear dependencies among the columns. It defines " +
                "an isometry between their ranges through the quotient by the kernel, and " +
                "finite-dimensional isometry extension supplies U. Rank-deficient matrices " +
                "and empty column types are included."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a = F.Id("A"), b = F.Id("B"), u = F.Id("U");
        return Disp(Seq(Forall, Sp, a, Comma, b, Colon, Sp,
            Call("Matrix", F.Id("m"), F.Id("n"), F.Id("Complex")), Comma, Esc,
            Call("gram", b), Sp, Eq, Sp, Call("gram", a), Sp, Implies, Esc,
            Exists, Sp, u, Colon, Sp, Call("Unitary", F.Id("m"), F.Id("Complex")), Comma, Sp,
            b, Sp, Eq, Sp, u, Sp, a));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
