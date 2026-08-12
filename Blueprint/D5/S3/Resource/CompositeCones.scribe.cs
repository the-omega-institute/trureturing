using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class CompositeConesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For finite complex matrices, separable, positive-semidefinite, and block-positive cones form a proved inclusion chain.",
        H("The Inclusion Chain of Composite Matrix Cones"),
        Blocks(
            Paragraph(Text(
                "For a bipartite finite-dimensional system there are three nested cones of "
                + "finite complex matrices: separable, positive semidefinite, and block positive, "
                + "where block positivity means nonnegativity on every product vector. "
                + "Separability is the strongest condition and block positivity the weakest.")),
            Paragraph(Text(
                "This module proves only the two inclusions; neither inclusion is proved proper, "
                + "and no witness is exhibited. The source atom writes proper-inclusion symbols, "
                + "but this formalization does not establish that a positive semidefinite matrix "
                + "can fail to be separable or that a block-positive matrix can fail to be "
                + "positive semidefinite.")),
            Paragraph(Text(
                "The first inclusion follows because a Kronecker product of positive semidefinite "
                + "factors is positive semidefinite and a finite sum of such matrices remains "
                + "positive semidefinite. The second is weaker because block positivity tests the "
                + "quadratic form only on the smaller set of product vectors, whereas positive "
                + "semidefiniteness gives nonnegativity on every vector.")),
            Paragraph(Text(
                "The proof reuses the library lemmas Matrix.PosSemidef.kronecker, "
                + "Matrix.posSemidef_sum, and Matrix.PosSemidef.re_dotProduct_nonneg; these "
                + "library-search results are recorded in the Lean source rather than reproved "
                + "locally. No physical interpretation involving entanglement, witnesses, or "
                + "separability testing is asserted.")),
            Describe.Lean(
                DescribeId.Create("separable-cone-is-a-finite-sum-of-psd-kronecker-products"),
                DeclarationHandle.Create("D5/S3/Resource/CompositeCones.separableCone"),
                H("The separable cone is a finite sum of PSD Kronecker products"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("separableCone")), F.Open,
                    F.Id("W"), F.Close, F.Leftrightarrow, F.Sp,
                    F.Exists, F.Sp, F.Id("k"), F.InMacro, F.Sp, F.Mathbb,
                    F.Grp(F.Id("N")), F.Comma, F.Sp,
                    F.Exists, F.Sp, F.Id("A"), F.Comma, F.Sp,
                    F.Exists, F.Sp, F.Id("B"), F.Comma, F.Sp,
                    F.Open, F.Forall, F.Sp, F.Id("i"), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Id("A"), F.Open, F.Id("i"), F.Close, F.Close,
                    F.Sp, F.Land, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Id("B"), F.Open, F.Id("i"), F.Close, F.Close,
                    F.Close, F.Sp, F.Land, F.Sp,
                    F.Id("W"), F.Eq, F.Sum, F.Sp, F.Id("i"), F.Sp,
                    F.InMacro, F.Sp, F.Operatorname, F.Grp(F.Id("Fin")),
                    F.Open, F.Id("k"), F.Close, F.Sp,
                    F.Id("A"), F.Open, F.Id("i"), F.Close, F.Times, F.Sp,
                    F.Id("B"), F.Open, F.Id("i"), F.Close,
                    F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A matrix belongs to the separable cone exactly when some finite family of "
                    + "positive semidefinite matrices A and B represents it as the sum over Fin k "
                    + "of their Kronecker products. The index size k may be zero."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("block-positive-means-nonnegative-on-product-vectors"),
                DeclarationHandle.Create("D5/S3/Resource/CompositeCones.blockPositive"),
                H("Block positivity tests every product vector"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("blockPositive")), F.Open,
                    F.Id("W"), F.Close, F.Leftrightarrow, F.Sp,
                    F.Forall, F.Sp, F.Id("a"), F.Comma, F.Sp,
                    F.Id("b"), F.Comma, F.Sp, F.D(0), F.Leq, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Re")), F.Open,
                    F.Operatorname, F.Grp(F.Id("dotProduct")), F.Open,
                    F.Id("a"), F.Times, F.Sp, F.Id("b"), F.Comma, F.Sp,
                    F.Id("W"), F.Open, F.Id("a"), F.Times, F.Sp, F.Id("b"), F.Close,
                    F.Close, F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A matrix is block positive when the real part of its quadratic form is "
                    + "nonnegative on every vector formed pointwise from a vector a on the first "
                    + "finite index set and a vector b on the second."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("separable-cone-is-contained-in-the-positive-semidefinite-cone"),
                DeclarationHandle.Create("D5/S3/Resource/CompositeCones.separable_isPosSemidef"),
                H("Separable matrices are positive semidefinite"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("m"), F.Comma, F.Sp, F.Id("n"), F.Comma,
                    F.Sp, F.Id("W"), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("separableCone")), F.Open,
                    F.Id("W"), F.Close, F.Sp, F.Rightarrow, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Id("W"), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every separable matrix is positive semidefinite. The proof applies the "
                    + "Kronecker-product lemma to each pair of PSD factors and then the finite-sum "
                    + "lemma to the resulting family."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("positive-semidefinite-matrices-are-block-positive"),
                DeclarationHandle.Create("D5/S3/Resource/CompositeCones.posSemidef_blockPositive"),
                H("Positive semidefinite matrices are block positive"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("m"), F.Comma, F.Sp, F.Id("n"), F.Comma,
                    F.Sp, F.Id("W"), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Id("W"), F.Close, F.Sp, F.Rightarrow, F.Sp,
                    F.Operatorname, F.Grp(F.Id("blockPositive")), F.Open,
                    F.Id("W"), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive semidefinite matrix is block positive because its quadratic "
                    + "form has nonnegative real part on all vectors, hence on the special product "
                    + "vectors used by the block-positive definition."))),
                DescribeRole.Theorem
            ))));
}
