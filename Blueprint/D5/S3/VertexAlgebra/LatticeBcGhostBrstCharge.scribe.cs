using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostBrstChargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostBrstCharge.";
    private static readonly LibraryNoteRef LatticeSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact actual matter and ghost tensor summands of the algebraic BRST charge.",
        H("Actual Lattice and Ghost Tensor BRST Charge"),
        Blocks(
            Paragraph(Text("D is any finite-rank even integral symmetric lattice, rank zero "
                + "included, and H is any complex matrix of its rank. U_D is the existing "
                + "all-charge lattice Carrier(D) tensor over Complex with the actual ghost "
                + "Fock(Complex). These are algebraic states, not a Hilbert completion; "
                + "no analytic convergence assertion is made. No positivity, inverse-Gram "
                + "identity, rank 26, centrality "
                + "or nilpotence premise is imposed for this construction.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcharge-matter-cutoff"),
                DeclarationHandle.Create(Prefix + "matterCutoff"),
                H("The actual Laurent order supplies the matter upper tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(Paragraph(Text("R(u)=-order(sugawaraField(D,H)u)-2, where order is "
                    + "the total HahnSeries order of the actual Laurent series. The actual "
                    + "sugawaraMode at n is the normalized n+1 coefficient, hence its raw "
                    + "exponent is -n-2. For n>R(u) that exponent is below the order and "
                    + "the mode vanishes. Total order is zero on the zero series: no "
                    + "attempt is made to untop its orderTop. The coefficient-vanishing "
                    + "theorem includes this zero case."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcharge-actual-summand"),
                DeclarationHandle.Create(Prefix + "A"),
                H("The exact actual tensor summand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("M_n is TensorProduct.map(sugawaraMode(D,H,n),id), "
                    + "G_n is TensorProduct.map(id,L_n), and C_q is TensorProduct.map(id,c_q). "
                    + "N_n=C_-n composed with G_n for n>=-1, and G_n composed with C_-n "
                    + "for n<=-2. A_n=C_-n composed with M_n plus (1/2)N_n. "
                    + "These are the actual endomorphisms, not assumed mode relations. "
                    + "There is no additional -c_0 in this SL2 vacuum convention."))),
                DescribeRole.Definition),
            Paragraph(Text("The classical convention is the SL2-invariant vacuum of "
                + "Maccaferri, Marino and Valsesia, Introduction to String Theory, "
                + "arXiv 2311.18111v2, sections 3.3.2-3.3.3, printed pages 76-80, "
                + "especially equation (3.286). The formal coefficient is fixed by the "
                + "actual mode definitions as n-k. This refers to that arXiv version, "
                + "not an independently checked journal version.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcharge-all-state-support"),
                DeclarationHandle.Create(Prefix + "A_finite"),
                H("Finite outer support on every actual tensor state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matter summand on u tensor g is supported "
                    + "in [-B(g)-2,R(u)]. The actual ghost joint-support rectangle supplies "
                    + "the outer bound [-B(g)-2,2B(g)+4]. Thus the support of A_n(u tensor g) "
                    + "lies in [-B(g)-2,max(R(u),2B(g)+4)]. Tensor induction extends "
                    + "pointwise finiteness to every state. This finite-support proof directly "
                    + "consumes the original BcGhostStressTails.outer_has_finite_support, "
                    + "not a duplicated ghost finiteness proof. Zero has empty support, pure "
                    + "tensors have this explicit interval, and addition has support "
                    + "contained in the union of the two finite input supports. "
                    + "No finite support in the space of endomorphisms is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcharge-q"),
                DeclarationHandle.Create(Prefix + "Q"),
                H("The actual linear algebraic BRST charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Q psi is the pointwise finsum over all integers "
                    + "of A_n psi. Its defining linear-map proofs use the established "
                    + "all-state finite support: addition distributes the finsum over "
                    + "the two finite state supports, and scalar multiplication commutes "
                    + "with each finite pointwise sum. Q is not an operator-space finsum "
                    + "of Module.End, and no additional -c_0 is inserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcharge-pure-tensor-expanded"),
                DeclarationHandle.Create(Prefix + "Q_tmul_expanded"),
                H("Exact pure-tensor and finite double-sum evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Q(u tensor g) equals the finite matter sum "
                    + "over n in [-B(g)-2,R(u)] of sugawaraMode(D,H,n)u tensor c(-n)g, "
                    + "plus one half of the actual ghost double sum over n in "
                    + "[-B(g)-2,2B(g)+4] and k in [-(3B(g)+8),3B(g)+8] of "
                    + "(n-k) times u tensor expanded(g,(n,k)). The summand preserves "
                    + "the stated c/L order in both branches. Q_tmul also evaluates "
                    + "the full summand on the common outer interval "
                    + "[-B(g)-2,max(R(u),2B(g)+4)]. Empty matter intervals and the zero "
                    + "Laurent series are included. These evaluation identities explain "
                    + "the construction, not a new physical realization or novelty claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrstcharge-ward-identity"),
                DeclarationHandle.Create(Prefix + "ward_identity"),
                H("The full actual tensor Ward anticommutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite-rank lattice D, arbitrary complex "
                    + "matrix H and integer m, the actual endomorphisms satisfy "
                    + "Q B_m + B_m Q = M_m + G_m on every algebraic tensor state. "
                    + "The two ordered branches of N are calculated using the released "
                    + "ghost mixed CAR and stress/current covariance. Comparing the "
                    + "n>=-1 branch with the m+n<=-2 normal-pair branch uses CAR; a "
                    + "threshold mismatch forces m!=0, so no scalar term survives. "
                    + "For m=0 the thresholds agree. The complete anticommutator is "
                    + "summed on its finite state support before the Kronecker and "
                    + "normal-pair terms are separated. The weighted normal-pair row "
                    + "sums to G_m by the original ghost definition and tensor induction. "
                    + "Thus two half contributions combine to the full G_m. This needs "
                    + "neither inverse-Gram assumptions, Virasoro relations, rank 26, "
                    + "nor nilpotence, and it does not take a global operator-space finsum."))),
                DescribeRole.Theorem),
            Paragraph(Text("No Q-square anomaly, nilpotence, BRST cohomology, no-ghost "
                + "theorem, complete string theory or AdS/CFT result is asserted. "
                + "A subsequent Q-square calculation requires both H*gramComplex(D)=1 "
                + "and gramComplex(D)*H=1, as well as actual matter and ghost Virasoro "
                + "proofs. Those hypotheses are not needed for this construction and "
                + "are not silently assumed here.")))));
}
