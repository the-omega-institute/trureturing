using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qLiftAnomalyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qLiftAnomaly.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-period lift commuting with charge inversion fixes every fixed-charge ground state. The P48q spectral premises then give cyclic type one at period three.",
        H("Fixed-Charge Lift Rigidity and the P48q Cyclic Type"),
        Blocks(
            Paragraph(Text("Let D be lattice data of rank r with integral symmetric Gram matrix and even diagonal, "
                + "L=Z^r its charge lattice with bilinear form B, and V the actual finite-support carrier "
                + "of complex oscillator polynomials. Write e_a=single(a,1) for the nonzero ground state of charge a. "
                + "The canonical ground normalization and its inclusion into V give the actual mode identity "
                + "(Y(e_a))_(-B(a,b)-1) e_b=epsilon(a,b) e_(a+b), where epsilon(a,b) is the nonzero "
                + "sign of the existing lattice cocycle.")),
            Describe.Lean(
                DescribeId.Create("odd-period-fixed-charge-phase"),
                DeclarationHandle.Create(Prefix + "fixed_charge_phase_eq_one_of_odd_period"),
                H("Odd operator period forces trivial fixed-charge multipliers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("Let g be an additive equivalence of L and U and I complex-linear equivalences of V. "
                        + "Suppose U(e_a)=eta(a)e_(g(a)) and I(e_a)=theta(a)e_(-a) for all a, with arbitrary "
                        + "complex units eta(a) and theta(a). Assume U preserves every integer vertex mode, "
                        + "so U((Y(u))_m v)=(Y(U(u)))_m U(v) for all u,v in V and m in Z. "
                        + "If UI=IU and U^n=1 for an odd natural number n, then eta(a)=1 whenever g(a)=a.")),
                    Paragraph(Text("For fixed charges b,c, the normalized ground mode and cancellation of the nonzero "
                        + "cocycle sign and ground state give eta(b+c)=eta(b)eta(c). Thus eta(0)=1 and "
                        + "eta(a)eta(-a)=1 on fixed charges. Commutation applied to e_a gives "
                        + "theta(a)eta(-a)=eta(a)theta(a), so cancellation of the arbitrary unit theta(a) "
                        + "gives eta(-a)=eta(a). Hence eta(a)^2=1. Applying the operator period to the fixed "
                        + "ground line gives eta(a)^n=1. The order of eta(a) divides both 2 and n and therefore "
                        + "divides 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-order-three-type-one"),
                DeclarationHandle.Create(Prefix + "p48q_order_three_type_one"),
                H("The P48q spectral premises force type one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("Nebe, arXiv:1312.3780, Table 1 lists P48q among the extremal even unimodular "
                        + "lattices of rank 48. Table 2 lists P48q as an example of the order-three lattice "
                        + "automorphism type 3-(16,16)-16, with fixed rank 16. Section 2 gives the prime-order "
                        + "rank decomposition. In the order-three specialization the two nontrivial complex "
                        + "eigenspaces have the same dimension p, giving fixedRank+2p=r.")),
                    Paragraph(Text("Gemünden–Keller, arXiv:1909.09626, equation (62) defines a standard lift by "
                        + "trivial action on fixed-charge ground states. In their positive-definite standard-lift "
                        + "twisted-module setting, the Heisenberg weight of equation (113) is the twisted lowest "
                        + "weight when the zero-momentum ground space is present. Equation (24) defines cyclic "
                        + "type as n^2 rho modulo n. "
                        + "The Lean theorem assumes the rank 48, fixedRank=16 and the rank decomposition as numerical "
                        + "premises. It also assumes that trivial fixed-charge phases imply the specialized standard-lift "
                        + "lowest-weight formula rho=(1*(3-1)*p+2*(3-2)*p)/(4*3^2), with rho rational.")),
                    Paragraph(Text("Under these premises and the preceding lift hypotheses with U^3=1, Lean proves "
                        + "p=16 by the rank equation and forces standard fixed-charge normalization by odd-period rigidity. "
                        + "The assumed weight formula then gives rho=16/9 and 3^2 rho=16. For every integer t "
                        + "representing 3^2 rho, Lean proves that its image in ZMod 3 is 1. This establishes the stated residue, "
                        + "which is type one under the cited cyclic type convention. The application to P48q uses "
                        + "the identification of g with an isometry having the cited spectral data and the "
                        + "identification of rho with its standard-lift twisted lowest weight. The theorem takes "
                        + "the numerical data and weight formula as premises."))),
                DescribeRole.Theorem))));
}
