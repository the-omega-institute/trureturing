using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalOcticSplitDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split determinant of the original octic window is irreducible over every characteristic-zero splitting field.",
        H("The labeled octic window"),
        Blocks(
            Paragraph(Text("Let alpha be an element of a field D with alpha to the eighth power equal to two. Let sigma_0 through sigma_7 be embeddings into a characteristic-zero field k. Fix a primitive eighth root zeta in k and preserve the labels sigma_i(alpha)=sigma_0(alpha) zeta^i. The four columns are the images of 1, alpha, alpha^3 and alpha^4 in that order. The polynomial is the determinant of the eight columns [B | diag(q) B], with rows labeled zero through seven.")),
            Describe.Lean(DescribeId.Create("normalized-coefficient-count"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count"),
                H("The exact normalized coefficient count"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are seventy four-element label sets. The normalized integer coefficient function vanishes at eighteen of them. Its other values belong to the set consisting of plus or minus one, two and four."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("original-determinant-structure"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure"),
                H("Structure of the actual determinant"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This statement derives homogeneity of degree four, degree at most one in each variable and exactly eighteen zero squarefree quartic coefficients from the root relations themselves.")),
                    Paragraph(Text("Put s=zeta+zeta^3, so s squared equals minus two. If U is the matrix of the first four rows of B, the last four rows are R U, where the rows of R are (-1,-s,2,s), (-s,1,s,0), (0,-s,1,s) and (-s,2,s,-1). The square of det(U) is 128. Block elimination expresses the eight-by-eight determinant as 128 times the determinant whose entry (i,j) is R(i,j)(q_(4+i)-q_j). Expanding this four-by-four determinant gives precisely the normalized integer coefficients counted above. No row permutation changes the original labels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-determinant-irreducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible"),
                H("Irreducibility with the original embeddings"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Applying each embedding to alpha^8=2 identifies its row with the root matrix used in the structure theorem. The homogeneous multiaffine quartic obstruction applies because eighteen is less than twenty. Thus the actual determinant is irreducible over k. The statement quantifies every characteristic-zero field containing these embeddings and the primitive root, so it also applies after further field extension.")),
                    Paragraph(Text("The original field element, its four powers and all eight embedding labels remain explicit. This determinant statement does not assert a classification of rational windows with equal quotient support."))),
                DescribeRole.Theorem))));
}
