using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class CompositeConePropernessDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/Resource/CompositeConeProperness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exchange operator and the unnormalized antisymmetric singlet witness the properness of both inclusions in the composite matrix-cone chain.",
        H("Properness of the Composite Matrix-Cone Inclusions"),
        Blocks(
            Paragraph(Text(
                "This module closes an open left by the frozen CompositeCones module. That module "
                + "said of itself: \"The source writes the chain with PROPER inclusion symbols, "
                + "SEP subset PSD subset SEP*. This module proves only the two INCLUSIONS. That "
                + "either of them is proper ... is NOT established here and no witness is "
                + "exhibited.\" What was missing was precisely a witness, and the present module "
                + "supplies one for each inclusion.")),
            Paragraph(Text(
                "The elegant point is that one matrix does both jobs. The exchange operator SWAP "
                + "is itself the block-positive-but-not-positive-semidefinite witness, and it is "
                + "also the entanglement witness that certifies the singlet matrix is not "
                + "separable. Thus the same separating functional resolves both properness "
                + "directions.")),
            Describe.Lean(
                DescribeId.Create("the-exchange-operator-is-block-positive"),
                DeclarationHandle.Create(LeanPrefix + "swapMatrix_blockPositive"),
                H("The exchange operator is block positive"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("blockPositive")), F.Open,
                    F.Operatorname, F.Grp(F.Id("swapMatrix")), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a product vector a times b, the quadratic form of SWAP is the squared "
                    + "absolute value of the sum over i of conjugate(a_i)b_i. This expression is "
                    + "manifestly nonnegative, so the exchange operator is block positive."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-exchange-operator-is-not-positive-semidefinite"),
                DeclarationHandle.Create(LeanPrefix + "swapMatrix_not_posSemidef"),
                H("The exchange operator is not positive semidefinite"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Neg, F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Operatorname, F.Grp(F.Id("swapMatrix")), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The antisymmetric vector e_01 - e_10 is an eigenvector of SWAP with "
                        + "eigenvalue minus one. Its quadratic form is therefore negative, which "
                        + "rules out positive semidefiniteness.")),
                    Paragraph(Text(
                        "A tempting substitute does not work: the Bell vector e_00 + e_11 is "
                        + "symmetric, SWAP fixes it, and its quadratic form is plus two. Only the "
                        + "antisymmetric singlet is detected. This trap was checked by compiling "
                        + "a temporary Lean audit before the module was written and was also "
                        + "recomputed independently as a numerical matrix calculation."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("a-block-positive-matrix-need-not-be-positive-semidefinite"),
                DeclarationHandle.Create(LeanPrefix + "exists_blockPositive_not_posSemidef"),
                H("A block-positive matrix need not be positive semidefinite"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Exists, F.Sp, F.Id("W"), F.Colon, F.Sp, MatrixType(), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("blockPositive")), F.Open, F.Id("W"), F.Close,
                    F.Sp, F.Land, F.Sp, F.Neg,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open, F.Id("W"), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking W to be swapMatrix combines the preceding two theorems. Consequently "
                    + "the positive-semidefinite cone is a proper subset of the block-positive "
                    + "cone SEP*."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-unnormalized-singlet-matrix-is-positive-semidefinite"),
                DeclarationHandle.Create(LeanPrefix + "singletMatrix_posSemidef"),
                H("The unnormalized singlet matrix is positive semidefinite"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Operatorname, F.Grp(F.Id("singletMatrix")), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The singlet matrix is the rank-one outer product of e_01 - e_10 with its "
                    + "conjugate and is therefore positive semidefinite. It is deliberately the "
                    + "unnormalized singlet, equal to twice the normalized rank-one projector. "
                    + "Positive scaling preserves both positive semidefiniteness and "
                    + "nonseparability, while this choice removes all square-root arithmetic."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-unnormalized-singlet-matrix-is-not-separable"),
                DeclarationHandle.Create(LeanPrefix + "singletMatrix_not_separable"),
                H("The unnormalized singlet matrix is not separable"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Neg, F.Operatorname, F.Grp(F.Id("separableCone")), F.Open,
                    F.Operatorname, F.Grp(F.Id("singletMatrix")), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The detector is again SWAP. For positive semidefinite factors C and D, "
                        + "the trace of SWAP times the Kronecker product C times D equals the trace "
                        + "of CD, whose real part is nonnegative. Every finite sum admitted by the "
                        + "definition of separability must therefore have a nonnegative detector "
                        + "value.")),
                    Paragraph(Text(
                        "The unnormalized antisymmetric singlet instead has detector value minus "
                        + "two. No finite sum of positive-semidefinite Kronecker products can attain "
                        + "that value, so the singlet matrix is not separable. This is the second "
                        + "role of the same exchange operator used above.")),
                    Paragraph(Text(
                        "The argument stays at generality G. It does not use the duality theorem "
                        + "from the sibling CompositeConeDuality module, which has generality I; "
                        + "only the definition of separability and the two elementary trace facts "
                        + "are needed."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("a-positive-semidefinite-matrix-need-not-be-separable"),
                DeclarationHandle.Create(LeanPrefix + "exists_posSemidef_not_separable"),
                H("A positive semidefinite matrix need not be separable"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Exists, F.Sp, F.Id("W"), F.Colon, F.Sp, MatrixType(), F.Comma, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open, F.Id("W"), F.Close,
                    F.Sp, F.Land, F.Sp, F.Neg,
                    F.Operatorname, F.Grp(F.Id("separableCone")), F.Open, F.Id("W"), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Taking W to be singletMatrix combines its positive semidefiniteness with "
                        + "its failure of separability. Hence the separable cone SEP is a proper "
                        + "subset of the positive-semidefinite cone, completing the proper chain "
                        + "SEP subset PSD subset SEP*.")),
                    Paragraph(Text(
                        "All six displays are authored legally because no pinned projectable "
                        + "statement fixture exists for any of these declarations. Document "
                        + "construction records a ProjectionGap for each one."))),
                DescribeRole.Theorem
            ))));

    private static Formula MatrixType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("Matrix")), F.Open,
        FinTwoProduct(), F.Comma, F.Sp, FinTwoProduct(), F.Comma, F.Sp,
        F.Mathbb, F.Grp(F.Id("C")), F.Close);

    private static Formula FinTwoProduct() => F.Seq(
        F.Open, F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(2), F.Close,
        F.Sp, F.Times, F.Sp,
        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(2), F.Close, F.Close);
}
