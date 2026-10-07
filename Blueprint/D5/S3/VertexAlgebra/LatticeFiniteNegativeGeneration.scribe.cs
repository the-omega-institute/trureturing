using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeFiniteNegativeGenerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of actual lattice fields spans the entire lattice carrier by negative-mode words.",
        H("Finite Negative-Mode Generation of the Lattice Carrier"),
        Blocks(
            Paragraph(Text("Let D have finite rank r, an integral symmetric Gram matrix G "
                + "with even diagonal. Norm positivity and finite generation additionally require a positive-definite real Gram matrix. Rank zero "
                + "is included. Charges form L=(Fin(r) to Z), and the oscillator algebra "
                + "P is the complex multivariate polynomial algebra on Fin(r) times N. "
                + "The carrier V is the space of finite-support functions L to P, with "
                + "vacuum single(0,1). Write B(alpha,beta)=sum_i,j alpha_i G_ij beta_j "
                + "and Q(alpha)=B(alpha,alpha).")),
            Paragraph(Text("For each basis charge e_i the neutral field H_i has normalized "
                + "mode m acting on single(delta,p) as single(delta,h_i(m,delta)p). "
                + "For m<0 this polynomial operator multiplies by X(i,-m-1). For m=0 "
                + "it multiplies by the scalar B(e_i,delta). For m>0 it is "
                + "m times sum_j G_ij partial_(j,m-1). These modes extend linearly "
                + "to V. A polynomial contains finitely many oscillator variables, "
                + "so sufficiently large positive modes kill it; finite charge support "
                + "gives a statewise bound and hence a vertex operator. The charged "
                + "fields F_beta are the actual exponential and polynomial-translation "
                + "fields of Actual Lattice Creation Coefficients.")),
            Describe.Lean(
                DescribeId.Create("latticefinitenegativegeneration-bilinear-symmetric"),
                DeclarationHandle.Create(Prefix + "bilinear_symmetric"),
                H("bilinear symmetric"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every ordinary D and charges alpha,beta, B(alpha,beta)=B(beta,alpha), directly from symmetry of the integral Gram matrix. No positive-form or nondegeneracy premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticefinitenegativegeneration-bilinear-neg-left"),
                DeclarationHandle.Create(Prefix + "bilinear_neg_left"),
                H("bilinear neg left"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every ordinary D and charges alpha,beta, B(-alpha,beta)=-B(alpha,beta). This is integral bilinearity without any positive-form premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticefinitenegativegeneration-bilinear-neg-right"),
                DeclarationHandle.Create(Prefix + "bilinear_neg_right"),
                H("bilinear neg right"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every ordinary D and charges alpha,beta, B(alpha,-beta)=-B(alpha,beta). This is integral bilinearity without any positive-form premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticefinitenegativegeneration-norm-positive"),
                DeclarationHandle.Create(Prefix + "norm_positive"),
                H("norm positive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If the real Gram matrix is positive definite, every nonzero integral charge alpha has B(alpha,alpha)>0. The real quadratic-form inequality is transported through the exact integral cast; rank zero remains allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lattice-finite-negative-generation"),
                DeclarationHandle.Create(Prefix + "finite_negative_generation"),
                H("A finite field family generates every charge and oscillator state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every such D there exists a finite set S of charges "
                        + "such that the complex span of all finite right-nested words "
                        + "A_1[-n_1-1] ... A_k[-n_k-1] single(0,1) is V. Each A_j "
                        + "is either H_i for i in Fin(r), or the actual F_beta for beta "
                        + "in S. The empty word is the vacuum. Every n_j ranges over "
                        + "all natural numbers, and neither word length, charge nor "
                        + "oscillator degree is bounded.")),
                    Paragraph(Text("One may take S to be the union of the signed basis "
                        + "charges and A={alpha : for every i, |B(e_i,alpha)|<G_ii}. "
                        + "Positive definiteness makes the Gram-coordinate map "
                        + "alpha to (B(e_i,alpha)) injective. Its values on A lie in "
                        + "a product of finite integer intervals, so A is finite.")),
                    Paragraph(Text("For alpha outside A choose i with "
                        + "|B(e_i,alpha)|>=G_ii, and choose beta=e_i or -e_i with "
                        + "the sign of B(e_i,alpha). Put gamma=alpha-beta. Then "
                        + "B(beta,gamma)=|B(e_i,alpha)|-G_ii>=0, while "
                        + "Q(gamma)=Q(alpha)-2|B(e_i,alpha)|+G_ii<Q(alpha). "
                        + "Here G_ii>0. Thus strong induction on the nonnegative "
                        + "integer Q(alpha) reduces every charge to A, always "
                        + "respecting the nonnegative pairing needed by a negative mode.")),
                    Paragraph(Text("On a pure charge state the exact coefficient is "
                        + "F_beta[-B(beta,gamma)-1] single(gamma,1) = "
                        + "epsilon(beta,gamma) single(beta+gamma,1). The creation "
                        + "exponential has constant coefficient one, and the "
                        + "polynomial translation preserves one. The cocycle value "
                        + "is a sign, so its square is one and the scalar can be "
                        + "removed inside the complex span. Charges in A come "
                        + "directly from vacuum by the minus-one mode. The descent "
                        + "therefore places every single(alpha,1) in the same word span.")),
                    Paragraph(Text("Negative neutral modes multiply by every oscillator "
                        + "variable. Polynomial induction, linear combinations, and "
                        + "finite charge support now put every element of V in that "
                        + "span. For rank zero the charge group has one element, "
                        + "there are no oscillator variables, and vacuum already "
                        + "spans the carrier.")),
                    Paragraph(Text("Bakalov-Kac, Twisted Modules over Lattice Vertex "
                        + "Algebras, arXiv math/0402315v1, section 4.1, printed "
                        + "pages 8-9, equations (4.4), (4.5), (4.10), and (4.12), "
                        + "give the current and exponential realization. Theorem "
                        + "4.1 uses the all-charge family. The finite set and the "
                        + "sign-constrained descent stated here are a deduction "
                        + "from that realization and positive definiteness, rather "
                        + "than a finite-family assertion attributed to that locator."))),
                DescribeRole.Theorem))));
}
