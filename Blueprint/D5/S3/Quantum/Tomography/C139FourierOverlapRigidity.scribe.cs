using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class C139FourierOverlapRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three phase readouts on three spanning probe directions recover a complex cross-term vector.",
        H("C139 Fourier Cross-Term Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nine-phase-probes-recover-cross-term"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/C139FourierOverlapRigidity."
                        + "nine_phase_probes_recover_cross_term"),
                H("Nine common unit probes determine the Fourier cross term"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let ζ be a primitive cubic phase, B a three-coordinate Fourier "
                            + "window, and x,y the old and transformed cross-term columns. "
                            + "Assume the nine common probes, formed from the three directions "
                            + "(1,-1,0), (0,1,-1), and (1,-ζ,0) with phases ζ^r, all have "
                            + "zero signed real readout.")),
                    Paragraph(Text(
                        "The proof uses the zero-phase readout to eliminate the real part "
                            + "of each probe value and the first nontrivial cubic phase to eliminate "
                            + "its imaginary part. The first two directions give z0=z1=z2 for "
                            + "z=x-By; the third gives z0=conjugate(ζ)z1. Primitivity forces "
                            + "all three coordinates to vanish, hence x=By. "
                            + "The unitary identity B*B=I then gives y=B*x.")),
                    Paragraph(Text(
                        "This is the finite algebraic content of AURIC C139 continuation "
                            + "Theorem 1.4. It formalizes the cross-term recovery step and does "
                            + "not add any new physical readout, continuity assumption, or "
                            + "unframed projection domain."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(
                H("Three-phase rigidity for arbitrary actual input labels"),
                Blocks(
            Paragraph(Text(
                "The scalar declaration phase_zero also supplies the phase-separation step "
                    + "in the complete application of R5-011, Theorem 5.1. Here X is any type "
                    + "of actual history labels, H is a complex inner-product space of finite "
                    + "positive dimension d, and K is an arbitrary complex Hilbert space. "
                    + "The input a:X→H need not be injective, and b:X→K is initially just a "
                    + "function. Choose actual labels αj whose vectors Aj=a(αj) form a basis "
                    + "B indexed by Fin d. This is an arbitrary basis: neither orthogonality "
                    + "nor unit length is required. The actual labels βjr, r∈{0,1,2}, satisfy "
                    + "βj0=αj and a(βjr)=ζ^r Aj, where ζ=exp(2πi/3). These input equations "
                    + "and the basis are the fixed interface, not conclusions about b.")),
            Paragraph(Text(
                "On that interface the following conditions are equivalent to a unique "
                    + "complex-linear isometry V:H→K with V(a(x))=b(x) for every x∈X: "
                    + "C: b(βjr)=ζ^r b(αj) for every j,r; "
                    + "N: ‖a(x)‖²≤‖b(x)‖² for every x; and "
                    + "D: ‖b(x)−b(βjr)‖²≤‖a(x)−a(βjr)‖² for every x,j,r. "
                    + "Only the reference side has 3d positions; the other slot ranges over "
                    + "all actual input labels. N applies to the anchor labels too, so no "
                    + "separate anchor-norm assumption is needed. Descent through a, "
                    + "linearity of b, all-pairs isometry, and norm equality are not premises.")),
            Paragraph(Text(
                "Use the convention that the inner product is linear in its second "
                    + "argument. Put Bj=b(αj), e(x)=‖b(x)‖²−‖a(x)‖², and "
                    + "z(x,j)=⟨b(x),Bj⟩−⟨a(x),Aj⟩. Expanding D with norm_sub_sq, "
                    + "inner_smul_right and norm_smul gives "
                    + "e(x)+e(αj)≤2 Re(ζ^r z(x,j)). The cubic root has unit norm and "
                    + "1+ζ+ζ²=0. Summing the three bounds gives 3(e(x)+e(αj))≤0. "
                    + "N makes both summands nonnegative; since d≥1 supplies an anchor, "
                    + "e(x)=0 for every label. The three real readouts are now nonnegative "
                    + "and sum to zero, hence are all zero. Apply the original phase_zero "
                    + "with z=z(x,j), its cubic identity, star ζ=ζ² and star ζ·ζ=1. "
                    + "It gives z(x,j)=0; conjugate symmetry yields the source's equivalent "
                    + "orientation ⟨Bj,b(x)⟩=⟨Aj,a(x)⟩. Taking x=αk fixes the entire "
                    + "anchor Gram matrix, including its nonorthogonal entries.")),
            Paragraph(Text(
                "The parameter map to Basis.constr is B, scalar field ℂ, and the value "
                    + "function j↦Bj. Let L=B.constr ℂ (j↦Bj). Basis.constr_basis gives "
                    + "L(Aj)=Bj. Expanding a vector in B with Basis.sum_repr and "
                    + "Basis.constr_apply extends the recovered anchor rows to "
                    + "⟨b(x),L(u)⟩=⟨a(x),u⟩ for every x,u. Expanding the first argument "
                    + "as well gives ⟨L(u),L(v)⟩=⟨u,v⟩ for all u,v. "
                    + "LinearMap.isometryOfInner therefore equips exactly L with its "
                    + "isometry structure; no orthonormal replacement of the actual "
                    + "reference basis is made.")),
            Paragraph(Text(
                "For u=a(x), the mixed inner identity and the already derived norm "
                    + "equality imply ‖b(x)−L(a(x))‖²=0 by the same norm-subtraction "
                    + "identity. Positivity forces b(x)=L(a(x)). This eliminates every "
                    + "possible orthogonal residual in K, whose dimension is unrestricted. "
                    + "Basis.ext proves uniqueness because any representing linear map "
                    + "must take each Aj to Bj. Conversely, a representing complex-linear "
                    + "isometry gives C by linearity and gives N and D with equality. "
                    + "For all x,y it follows that ⟨b(x),b(y)⟩=⟨a(x),a(y)⟩, "
                    + "‖b(x)−b(y)‖=‖a(x)−a(y)‖, and a(x)=a(y) implies b(x)=b(y). "
                    + "Finite-dimensional completeness of H and Hilbert completeness of K "
                    + "permit LinearIsometry.adjoint_comp_self on the associated continuous "
                    + "linear map, giving V*V=I without requiring finite-dimensional K.")),
            Paragraph(Text(
                "The scalar identity phase_zero separates a single complex number; "
                    + "the representation conclusion also uses the basis construction, "
                    + "inner-product and norm identities, and the adjoint identity above. "
                    + "The complex geometry, common scale, actual phase labels and complete "
                    + "output are explicit assumptions. Complete output includes failure, stopping "
                    + "and leakage records. Memory and control settings that change a successor "
                    + "belong in its input or process label. The phase labels share an internal "
                    + "coherent reference; their bare rays alone do not supply the difference "
                    + "readouts required by D. In a direct sum of recorded outcomes, "
                    + "N and D concern the total squared norm, not each postselected branch. "
                    + "The conclusion is a mathematical extension of the declared inputs; "
                    + "it does not supply unprovided devices, coherent controls, arbitrary "
                    + "unprepared inputs, Kraus instruments or physical time. The 3d "
                    + "reference layout is a calibration compression, with no claim of "
                    + "strictly weaker physical laws, native experimental cost or literature "
                    + "priority.")))))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula() => Disp(Seq(
        Apply("primitiveCubicPhase", F.Id("zeta")), Sp, Land, Sp,
        Apply("fourierWindow", F.Id("B")), Sp, Land, Sp,
        Apply("ninePhaseProbeReadouts", F.Id("zeta"), F.Id("B"), F.Id("x"), F.Id("y")),
        Sp, Rightarrow, RowBreak,
        Apply("crossTermCovariance", F.Id("B"), F.Id("x"), F.Id("y")), Dot));
}
