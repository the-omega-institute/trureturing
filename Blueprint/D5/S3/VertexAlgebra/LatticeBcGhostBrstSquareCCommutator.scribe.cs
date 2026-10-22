using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostBrstSquareCCommutatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostBrstSquareCCommutator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual BRST square commutes with each c mode on the entire algebraic tensor state space.",
        H("All-State BRST Square c-Mode Commutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstsquareccommutator-c-mode-leg"),
                DeclarationHandle.Create(Prefix + "square_c_commutator"),
                H("The c-mode leg for arbitrary lattice and matrix data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let D be any original finite-rank even integral symmetric "
                        + "lattice, H any complex matrix indexed by Fin(D.rank), and p any "
                        + "integer. On the complete original algebraic tensor product "
                        + "State(D)=Carrier(D) tensor over Complex with Fock(Complex), "
                        + "the original operators satisfy (Q(D,H)Q(D,H))C(D,p) minus "
                        + "C(D,p)(Q(D,H)Q(D,H)) equals zero. This is an endomorphism "
                        + "identity, not an assertion restricted to a vacuum or to a "
                        + "bounded operator domain. Rank zero and every matrix fiber remain "
                        + "in scope. No inverse-Gram identity, rank 26, Virasoro identity, "
                        + "nilpotence premise, or finite-cutoff hypothesis is imposed.")),
                    Paragraph(Text("The existing full c_action gives "
                        + "Q C(q)+C(q) Q=-(1/2)V(q), where V(q)psi is the actual pointwise "
                        + "finsum of (2n+q)C(-n)C(n+q)psi. Ordinary associative algebra "
                        + "then gives [Q squared,C(p)]=-(1/2)[Q,V(p)] and "
                        + "[Q,C(a)C(b)]={Q,C(a)}C(b)-C(a){Q,C(b)}. Applying c_action "
                        + "to both factors gives -(1/2)(V(a)C(b)-C(a)V(b)). "
                        + "The proof retains both complete product terms before summing.")),
                    Paragraph(Text("For a ghost state g let S be the natural supremum of "
                        + "occupied(g), and take B=S+4. Every q>B uses the actual "
                        + "annihilation branch at the even site 2(q-2), strictly above S; "
                        + "hence c(q)g=0. Pure tensors inherit this upper-mode bound. "
                        + "Tensor induction gives a bound B>=1 for every State(D) vector, "
                        + "using the maximum of the two bounds at an addition step. "
                        + "This is an input-dependent bound, not an additional assumption "
                        + "or a globally finite operator family.")),
                    Paragraph(Text("The original c-c anticommutation law lifts to the "
                        + "actual tensor operators. Two adjacent interchanges give "
                        + "C(a)C(b)C(c)psi=C(b)C(c)C(a)psi with positive sign. If any "
                        + "mode exceeds B, a cyclic permutation moves it to the right, "
                        + "where it kills psi. For a+b+c=p, every nonzero triple therefore "
                        + "has all three modes in [p-2B,B]. The proof bounds the joint "
                        + "family on the finite cube filtered by this sum condition, "
                        + "represented by pairs (a,b) with c=p-a-b. This joint support "
                        + "is established before any nested finsum is flattened.")),
                    Paragraph(Text("Write J(a,b)=(2c-p)(b-a)C(a)C(b)C(c)psi, with "
                        + "c=p-a-b and integer coefficients mapped into Complex. "
                        + "The pair equivalence rho(a,b)=(b,p-a-b) cyclically permutes "
                        + "the modes and preserves their product on psi. Its inverse is "
                        + "rho inverse(a,b)=(p-a-b,a). The three scalar coefficients "
                        + "(2c-p)(b-a), (2a-p)(c-b), and (2b-p)(a-c) add to zero. "
                        + "Finite-support additivity and cyclic reindexing therefore "
                        + "give three times the sum of J equal to zero. Multiplication "
                        + "by the inverse of three in Complex makes that sum zero.")),
                    Paragraph(Text("Expanding [Q,V(p)] at psi gives the common factor "
                        + "-(1/2) times the difference of two joint state-vector sums. "
                        + "The first has modes (-k,k-n,n+p) and coefficient "
                        + "(2n+p)(2k-n). The equivalence (n,k) maps to (-k,k-n), "
                        + "with inverse (a,b) maps to (-a-b,-a), identifies it with J. "
                        + "The second has modes (-n,-k,k+n+p) and coefficient "
                        + "(2n+p)(2k+n+p). Under (n,k) maps to (-n,-k), its coefficient "
                        + "is minus the cyclic coefficient (2a-p)(c-b); consequently "
                        + "that whole row is minus J after rho. The subtraction of the "
                        + "second row therefore has the positive cyclic sign. Both "
                        + "joint sums vanish by the same Jacobi cancellation.")),
                    Paragraph(Text("The original V rows at psi and Q psi have actual "
                        + "finite support; linear-map postcomposition preserves it. "
                        + "These facts license moving Q through V and combining the "
                        + "complete commutator. The jointly finite triple arrays license "
                        + "every inner subtraction, scalar extraction, and product-index "
                        + "finsum conversion. No endomorphism-valued infinite sum or "
                        + "unsupported exchange of separately finite rows is used.")),
                    Paragraph(Text("This is an algebraic ingredient of the original BRST "
                        + "nilpotence route, with statement source given by the dispatch "
                        + "target. It is not a literature-novelty or physical-realization "
                        + "claim. It proves only the c-mode commutator assertion. "
                        + "It neither imports vacuum_square nor turns that vacuum-sector "
                        + "result into an all-state square-zero theorem. The b-mode leg, "
                        + "critical total covariance, and the creation-generation "
                        + "propagation to all ghost states require their own proofs. "
                        + "No tensor endomorphism is treated as a scalar ghost "
                        + "endomorphism by an unproved commutant bridge."))),
                DescribeRole.Theorem)
        )));
}
