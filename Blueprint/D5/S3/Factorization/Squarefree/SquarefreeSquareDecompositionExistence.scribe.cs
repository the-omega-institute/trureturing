using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Squarefree;

internal sealed class SquarefreeSquareDecompositionExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive natural number is uniquely a square times a squarefree number.",
        H("Existence and Uniqueness of the Square-Squarefree Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-natural-square-squarefree-exists-unique"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Squarefree/SquarefreeSquareDecompositionExistence."
                    + "bcs_square_squarefree_exists_unique"),
                H("Positive naturals have a unique square-squarefree decomposition"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    Exists, Bang, Sp, Open, F.Id("b"), Comma, Sp, F.Id("a"), Close,
                    Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp, Times, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("b"), Sp, Gt, Sp, D(0), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Squarefree")), Open, F.Id("a"), Close,
                    Sp, Land, Sp, F.Id("b"), Caret, Grp(D(2)), Sp, Cdot, Sp,
                    F.Id("a"), Sp, Eq, Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each positive natural n there is exactly one ordered pair (b, a) of "
                        + "natural numbers such that b is positive, a is squarefree, and b^2 * a = n. "
                        + "The ordering records the square root first and the squarefree part second.")),
                    Paragraph(Text(
                        "The proof reuses both available library results. Pinned Mathlib supplies the "
                        + "existence of a positive square-times-squarefree decomposition through "
                        + "Nat.sq_mul_squarefree_of_pos. The repository's existing theorem "
                        + "bcs_square_squarefree_unique proves that any two such decompositions agree. "
                        + "Combining them yields existence and uniqueness without reproving either half.")),
                    Paragraph(Text(
                        "This closes only the first assertion of residual remark 27.326: the BCS "
                        + "decomposition of positive naturals. It makes no claim about the k-free ladder, "
                        + "zeta identities, Mobius sums, Mertens behavior, or the Riemann hypothesis "
                        + "language that also appears in the source atom."))),
                DescribeRole.Theorem
            )),
        []));
}
