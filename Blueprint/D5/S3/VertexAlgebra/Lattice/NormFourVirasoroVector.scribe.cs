using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourVirasoroVectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A norm-four lattice state has all self-products and every integer Virasoro commutator at central charge one half.",
        H("The Actual Norm-Four Virasoro State"),
        Blocks(
            Paragraph(Text("Let D be a finite-rank lattice with integral symmetric Gram matrix and even diagonal. "
                + "Charges are maps from Fin(rank(D)) to Z, and the oscillator algebra is the complex "
                + "multivariate polynomial ring on Fin(rank(D)) times N. The carrier V is its finite-support "
                + "charge direct sum. Write B for the integral bilinear form, vacuum=single(0,1), T for the "
                + "charge-sensitive translation, and Y for the constructed lattice state-field map. "
                + "The normalized coefficient q is the Laurent coefficient at -q-1, and mu(u,q,w)=Y(u)_q(w).")),
            Paragraph(Text("For a charge a with B(a,a)=4 and a complex scalar s with s squared equal to one, "
                + "put A=sum_i a_i X(i,0), Q=single(0,A squared), E=single(a,1)+single(-a,1), "
                + "and v=(1/16)Q+(s/4)E. Thus both signs are included. Define L_m=Y(v)_(m+1). "
                + "The statement uses no positivity, rootlessness, unimodularity, nondegeneracy, "
                + "ambient conformal grading or additional rank assumption.")),
            Describe.Lean(
                DescribeId.Create("normfourvirasorovector-self-products"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector.self_products"),
                H("All actual singular self-products and the unbounded tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such D,a,s, the five conclusions hold simultaneously: "
                    + "mu(v,0,v)=T(v), mu(v,1,v)=2v, mu(v,2,v)=0, mu(v,3,v)=(1/4)vacuum, "
                    + "and mu(v,n,v)=0 for every integer n at least four. The proof evaluates the neutral, "
                    + "same-charge, opposite-charge and both mixed products in the actual carrier. "
                    + "The norm-four cocycle phase is one. Opposite charges cancel odd oscillator terms, "
                    + "and negative creation-series indices prove the entire tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normfourvirasorovector-virasoro-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector.virasoro_commutator"),
                H("Every integer mode satisfies the central-charge-one-half relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer m,n, L_m L_n-L_n L_m=(m-n)L_(m+n) "
                    + "plus ((m cubed-m)/24) times the identity when m+n=0, and zero central term otherwise. "
                    + "The supported actual mode-commutator formula and the self-products reduce the sum to "
                    + "indices zero through three. The integer binomial polynomial includes negative m+1; "
                    + "no nonnegative upper-index restriction is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normfourvirasorovector-opposite-sign-products"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector.opposite_sign_products"),
                H("Opposite signs in one norm-four direction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a norm-four charge and s² = 1, every nonnegative product "
                    + "of the states of signs s and −s vanishes. The mixed terms cancel, and the "
                    + "quadratic and charged terms cancel in degrees zero through three. Their "
                    + "higher products vanish by the self-product tail formulas."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normfourvirasorovector-orthogonal-products"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector.orthogonal_products"),
                H("Products of states in orthogonal directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For orthogonal charges and arbitrary scalars, all nonnegative "
                    + "mixed products vanish. Orthogonality removes the current contractions, and "
                    + "negative creation-coefficient indices give the ground-product vanishing."))),
                DescribeRole.Theorem),
            Paragraph(Text("The norm-four formula is classical: Shimakura, arXiv:1202.6107, page 4, equation (1.3), "
                + "attributes its Ising-vector assertion to Dong-Mason-Zhu, Theorem 6.3. The results here "
                + "give the self-products, the vanishing mixed products, and the mode action. The lattice-field "
                + "construction follows Bakalov-Kac, arXiv:math/0402315, section 4.1. Imported normal-product "
                + "and Sugawara sources retain Scott Carnahan and Kalle Kytola Apache-2.0 attribution.")),
            Paragraph(Text("These algebraic conclusions do not establish the simple minimal-model quotient, "
                + "simplicity, an ambient conformal vector, a Virasoro frame, Monster moonshine, "
                + "string theory or AdS/CFT.")))));
}
