using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class RationalKummerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total rational descent and explicit halving.",
        H("Total rational descent and explicit halving"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-kummer-curve"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.curve"),
                H("Split rational cubic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every rational D, curve D has coefficients a1=a3=a6=0, a2=-10D and a4=-75D squared. Its affine equation is y squared = x(x+5D)(x-15D)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-curve-is-elliptic"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.curve_is_elliptic"),
                H("Ellipticity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D, the displayed curve is elliptic. Its discriminant is 36000000 times D to the sixth power."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-root"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.root"),
                H("Ordered roots"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every rational D, the ordered roots are 0, -5D and 15D."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-explicit-half"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.explicit_half"),
                H("An explicit rational half"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For rational D,x,y,a,b,c with D nonzero, a squared=x, b squared=x+5D, c squared=x-15D and abc=-y, every nonsingular point (x,y) has the rational half (x+ab+ac+bc,-(a+b)(a+c)(b+c)). The conclusion constructs its nonsingularity proof and verifies doubling in the actual rational point group. None of a,b,c is required to be nonzero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-descentrep"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.descentRep"),
                H("Total descent representatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every rational D and each of the three ordered roots e, the representative at infinity is 1. At a finite point it is x-e when x differs from e, and 3e squared-20De-75D squared when x=e. Thus the zero-coordinate values are -75D squared, 100D squared and 300D squared, respectively."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-descentrep-add-square"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.descentRep_add_square"),
                H("Addition and square products"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D, every root index i and all actual rational points P,Q, the product of the total representatives at P, Q and P+Q is a rational square. The secant and tangent polynomial identities cover finite nonvertical sums; infinity and inverses complete the remaining cases. Replacing a zero coordinate by the root derivative preserves the square-product identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-squareclass"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.SquareClass"),
                H("Rational square classes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SquareClass is the existing quotient of rational units by the range of the square-power homomorphism. Zero is not a representative of this quotient."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-coordinate"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.coordinate"),
                H("Single-coordinate homomorphism"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D and ordered root index i, coordinate is an additive homomorphism from the actual rational point group to the additive form of rational units modulo squares. It uses the total nonzero descent representative."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-kummer"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.kummer"),
                H("The ordered Kummer pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D, kummer is the product of coordinates 0 and 1. At an ordinary affine point it is the ordered squareclass pair (x,x+5D). At infinity it is (1,1); the root exceptions use the total representatives."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-descentrep-product-square"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.descentRep_product_square"),
                H("The third coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D and every actual rational point, the product of all three total descent representatives is a rational square. Consequently the three square classes have product one, and the third class is the product of the first two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-kummer-zero-iff-double"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.kummer_zero_iff_double"),
                H("The complete doubling kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D and every actual rational point P, its Kummer pair is zero if and only if there exists an actual rational point Q with Q+Q=P. The reverse construction chooses the signs of three rational square roots so their product is minus the ordinate, then applies the explicit half formula. Infinity and every two-torsion root are included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-affine-double-iff"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.affine_double_iff"),
                H("Affine squarehood criterion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero rational D and nonsingular affine point (x,y), a rational doubling preimage exists if and only if x, x+5D and x-15D are rational squares. Squarehood includes zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-class-of"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.classOf"),
                H("The class of a nonzero rational"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonzero rational a, classOf a is its unit class modulo squares, in additive notation."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-kummer-block-images"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.block_kummer_images"),
                H("Block-coordinate images and odd multiples"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let D,C,L,F be nonzero rational numbers satisfying L squared+3=DC squared and L squared+4=5F squared. Suppose R=(5D(L squared+3),25D squared LCF) and S=(-15/C squared,75LF/C cubed) are actual nonsingular points on the displayed curve. Their Kummer images are ([5],[D]) and ([-15],[5]), respectively. Every integer odd multiple (2n+1)S has the latter image, including negative odd multiples. The proof supplies unit-square witnesses DC, 5F, 1/C and L/C for the four coordinate comparisons.")),
                    Paragraph(Text("The image statement retains its two curve-membership hypotheses. The block translation theorem derives those memberships and identifies the translate from the two displayed algebraic identities."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-kummer-block-translation"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/RationalKummer.block_translation"),
                H("The original translation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let D,C,L,F be rational numbers with C nonzero, L squared+3=DC squared and L squared+4=5F squared. These identities force D nonzero. They construct nonsingularity proofs for R=(5D(L squared+3),25D squared LCF), T0=(0,0) and S=(-15/C squared,75LF/C cubed). In the actual rational point group, R+T0=S. The slope from R to T0 is 5LF/C, and its addition coordinates are exactly those displayed for S.")),
                    Paragraph(Text("For an original golden block, take N=3 to the power j with j at least one, L=goldenLucas N and F=Nat.fib N. The existing Lucas discriminant identity gives L squared+4=5F squared because N is odd. The Lucas-Fibonacci bridge gives L positive, and this identity forces F nonzero. A positive integer C and the block equation B=L squared+3=DC squared therefore meet all hypotheses above and of the image theorem. Thus the original R and S have images ([5],[D]) and ([-15],[5]); every integer odd multiple of either has the same image as that point. Here T0 has image ([-3],[5D]), its third coordinate is [-15D], and the three quotient coordinates have product one. The third coordinate at every point is the product of the first two.")),
                    Paragraph(Text("These descent statements do not determine a full two-Selmer group, a Cassels pairing, a rational rank, nonsingular reduction subgroups, generators, or denominator and integrality bounds."))), DescribeRole.Theorem))));
}
