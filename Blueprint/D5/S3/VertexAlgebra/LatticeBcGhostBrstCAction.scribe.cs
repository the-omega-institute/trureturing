using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostBrstCActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostBrstCAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual BRST c-current variation on the full algebraic lattice and ghost tensor carrier.",
        H("Actual BRST c-Current Variation"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank even integral symmetric lattice, "
                + "including rank zero, let H be any complex matrix indexed by Fin(D.rank), "
                + "and let p be any integer. The state space is the complete algebraic "
                + "tensor product Carrier(D) tensor over Complex with Fock(Complex). "
                + "Q, A, N, C, M and G are the existing actual operators. The assertion "
                + "does not restrict states to the vacuum or truncate their operator domain.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcaction-row-operator"),
                DeclarationHandle.Create(Prefix + "V"),
                H("The pointwise finite c-c row defines a linear operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every state psi, V(D,p)psi is the finsum over "
                    + "integers n of (2n+p) times C(-n)C(n+p)psi. This is a sum of state "
                    + "vectors, not a sum in the endomorphism space. For a ghost state g "
                    + "write S=sup(occupied(g)) and R=S+abs(p)+4. If n>R, then c(n+p) "
                    + "is an annihilator at the site 2(n+p-2), strictly above S, and "
                    + "kills g. If n<-R, the same argument applies to c(-n); the "
                    + "signed c-c anticommutation relation moves that annihilator to "
                    + "the right before it acts on g. Hence the unweighted ghost row "
                    + "is supported in [-R,R]. Multiplication by 2n+p cannot enlarge "
                    + "the support. Pure tensors inherit this finite support, and tensor "
                    + "induction extends finiteness to every algebraic state. Additivity "
                    + "and complex linearity follow from finite-support finsum identities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcaction-full-variation"),
                DeclarationHandle.Create(Prefix + "c_action"),
                H("The full Q-c anticommutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, H and p in the stated telescope, "
                    + "Q(D,H)C(D,p)+C(D,p)Q(D,H) equals -(1/2)V(D,p) as an actual "
                    + "linear endomorphism of the entire tensor state space. The matter "
                    + "operator M commutes with C, so the C(-n)M(n) contribution has "
                    + "zero anticommutator with C(p). Ghost covariance gives "
                    + "[G(n),C(p)]=(-2n-p)C(n+p). For n>=-1 the ordered ghost term is "
                    + "C(-n)G(n); for n<=-2 it is G(n)C(-n). In the second branch, "
                    + "c-c anticommutation reverses C(n+p)C(-n), giving the same "
                    + "coefficient -(2n+p) in both branches. Consequently the complete "
                    + "A(n)-C(p) anticommutator is -(1/2)(2n+p)C(-n)C(n+p). "
                    + "The already finite A rows at psi and C(p)psi justify moving "
                    + "C(p) through Q and combining the two complete summands. Their "
                    + "statewise sum is exactly -(1/2)V(D,p)psi. No unsupported "
                    + "infinite matter or ghost summand is separated."))),
                DescribeRole.Theorem),
            Paragraph(Text("The normalization is fixed by the existing signed ghost modes "
                + "and the actual algebraic BRST charge. This is an algebraic consequence "
                + "in that model, not a claim of literature novelty or of a new physical "
                + "realization. No inverse-Gram identity, rank 26, matter or ghost Virasoro "
                + "relation, or nilpotence premise is used. The c-current variation is "
                + "one ingredient of a subsequent Q-square computation; it does not "
                + "prove Q-square vanishing, BRST cohomology or complete string theory."))
        )));
}
