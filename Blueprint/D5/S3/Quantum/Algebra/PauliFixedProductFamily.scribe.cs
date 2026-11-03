using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliFixedProductFamilyDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Pow(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Abs(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(V(name)), Open,
            Seq(args.SelectMany((x,i) => i == 0 ? new[] {x} : new[] {Comma,x}).ToArray()), Close);
    private static DocumentBlock Theorem(string name, string heading, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-')),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliFixedProductFamily." + name),
            H(heading), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed spin products carry an actual real Pauli perturbation with sharp local data and a complete unaveraged residual.",
        H("Fixed positive tensor product and the complete Pauli residual"),
        Blocks(
            Paragraph(Text("The local space is real Euclidean four-space, ordered as scalar, x, y, z. "
                + "Its spin multiplication sends (a,v),(b,w) to (ab+v dot w, aw+bv), and its fixed cross channel sends them to (0,v cross w). "
                + "The action D(t) replaces the first cross label v by v+taz, for every real t. The local Euclidean inner product and multiplication are fixed. "
                + "The joint carrier is the actual real Hilbert tensor product with its positive product inner product.")),
            Paragraph(Text("On pure tensors, the joint multiplication is spin tensor spin minus cross tensor cross. "
                + "The cross channels in that multiplication remain fixed. The actual joint action on a simple label is D tensor left multiplication "
                + "plus left multiplication tensor D. Bilinear maps and the tensor universal property extend the definitions to every joint input. "
                + "The residual E is Gamma applied to the product minus the two terms obtained by applying Gamma to one product input. "
                + "No arbitrary residual table or global derivation law is assumed.")),
            Theorem("residual_scaling", "The actual residual scales on all joint inputs",
                Seq(Forall,Sp,V("t"),Comma,V("H"),Comma,V("X"),Comma,V("Y"),Comma,Sp,
                    Call("E",V("t"),V("H"),V("X"),V("Y")),Eq,V("t"),Sp,
                    Call("E",D(1),V("H"),V("X"),V("Y"))),
                "The local label action is affine in t, hence so are the actual joint action and its trilinear residual. "
                + "At t=0 the residual vanishes on the entire joint carrier. This follows from its exact values on the complete product basis "
                + "and trilinearity, extended through the basis span in each of the three slots. Therefore E(t,H,X,Y)=t E(1,H,X,Y) "
                + "for arbitrary H,X,Y, including arbitrary sums of pure tensors."),
            Theorem("full_report", "All ordered labels and every output coordinate",
                Seq(Forall,Sp,V("t"),Sp,InMacro,Sp,Mathbb,Grp(V("R")),Comma,Sp,
                    Call("reportSquared",V("t")),Eq,D(2,8,8),V("t"),Caret,Grp(D(2))),
                "The report sums squared output norms over all three copies of the complete sixteen-element product basis. "
                + "There is no average over its 4096 ordered triples; each output norm includes every output coordinate in the fixed positive product metric. "
                + "At parameter one, six first-input blocks contribute forty-eight each and all ten other first-input blocks vanish. "
                + "The block with first label 1 tensor z has zero rows when both second-input factors are 1 or z, and squared row sum four otherwise. "
                + "All block values are evaluated from the actual bilinear product and joint action, and all-input residual scaling gives 288t squared."),
            Theorem("family_contract", "The fixed realization satisfies all four original identities",
                Seq(Forall,Sp,V("t"),Comma,Sp,Call("fixedRealization",V("t"))),
                "The local dimension is four and the joint dimension is sixteen. The local basis is a complete orthonormal basis with elements 1,x,y,z, "
                + "and its tensor product is the complete joint orthonormal basis used by the report. The spin multiplication is commutative, has unit 1, "
                + "and is Frobenius. Every D(t,a) is an exact local derivation on all inputs, and D(t,x,y)=z shows activity for every t. "
                + "The fixed M is commutative, has unit 1 tensor 1, and is Frobenius for the same positive product inner product; "
                + "the squared self-inner-product is nonnegative and vanishes exactly at zero. "
                + "For all local a,b,c,d, M(a tensor 1,c tensor d)=S(a,c) tensor d and M(1 tensor b,c tensor d)=c tensor S(b,d). "
                + "For all the same inputs, Gamma(t,a tensor b,c tensor 1)=D(t,a,c) tensor b and "
                + "Gamma(t,a tensor b,1 tensor d)=a tensor D(t,b,d). The theorem also retains the exact complete residual square 288t squared. "
                + "These are identities of the actual maps, without alternation, Jacobi or vanishing of the unit generator as assumptions."),
            Paragraph(Text("The direct spin-factor construction establishes the required algebraic realization without a physical supply conclusion. "
                + "It proves no general stability theorem for arbitrary joint products, no acquisition procedure and no noisy reconstruction of physical objects.")),
            Paragraph(Text("All vectors, products, basis elements and actions are those of PauliFixedProductFamily. "
                + "Every assertion quantifies over every real t. A greatest value includes both a universal upper bound and an actual unit input attaining it. "
                + "The local Euclidean norm and multiplication stay fixed as t varies.")),
            Theorem("exact_defects", "Attained self-defect and unit-generator norm",
                Seq(Call("diagonalMaximum",V("t")),Eq,Seq(Frac,Grp(Abs(V("t"))),Grp(D(2))),Comma,Sp,
                    Call("unitMaximum",V("t")),Eq,Abs(V("t"))),
                "The self-defect ranges over every local unit vector a and is the norm of D(t,a,a). "
                + "Its greatest value is absolute t divided by two, attained at (1+x)/sqrt(2). "
                + "The unit-generator range uses every unit b and the norm of D(t,1,b); its greatest value is absolute t, attained at x. "
                + "For every a,b, the spin-product norm is at most sqrt(2) times norm(a) times norm(b), "
                + "and the action norm is at most sqrt(1+t squared) times the same two norms. "
                + "The proofs use exact nonnegative square decompositions in the original Euclidean coordinates."),
            Theorem("exact_constants", "All original local constants are sharp",
                Seq(V("u"),Eq,D(1),Comma,V("ell"),Eq,Root(D(2)),Comma,V("k"),Eq,D(1),Comma,
                    V("d"),Eq,Root(Seq(D(1),Plus,Pow(V("t"))))),
                "The unit has norm one. The sharp spin-product constant sqrt(2) is attained with both arguments (1+x)/sqrt(2). "
                + "The sharp action constant sqrt(1+t squared) is attained at the unit label (t1+z)/sqrt(1+t squared) and unit input x. "
                + "Curvature means the norm of [L(e_i),L(e_j)]e_k on the full original four-element basis. "
                + "Every such entry has norm at most one and [L(x),L(y)]y=x attains one. It is the specified finite-table maximum, "
                + "without identifying it with a maximum over arbitrary unit labels."),
            Theorem("exact_action_data", "The actual action Gram and its kernels",
                Seq(Call("G",V("t")),Eq,Call("diag",D(0),Seq(D(2),Plus,Pow(V("t"))),
                    Seq(D(2),Plus,Pow(V("t"))),D(2))),
                "The action Gram is the sum of adjoint(D(t,e_i)) composed with D(t,e_i) over all four basis labels. "
                + "Its displayed diagonal is an identity on every local vector. Its common fixed kernel is precisely the scalar axis. "
                + "The span of every actual table output is the spatial subspace a(0)=0. "
                + "The label kernel D(t,a)=0 is instead the line spanned by 1-tz. "
                + "A real lambda is an eigenvalue exactly when it is zero, 2+t squared, or 2. "
                + "The full diagonal also retains the multiplicities, including their collision at t=0."),
            Theorem("exact_label_data", "The distinct label Gram and exact positive spectral minimum",
                Seq(Call("positiveMinimum",Call("G",V("t"))),Eq,D(2)),
                "The label Gram is formed from the maps a maps to D(t,a,e_i), with adjoints in the same fixed Euclidean product. "
                + "Its coordinates are (2t squared a0+2t a3, 2a1, 2a2, 2t a0+2a3), so it is twice the matrix with "
                + "rows (t squared,0,0,t), (0,1,0,0), (0,0,1,0), (t,0,0,1). "
                + "Its eigenvalues are exactly zero, 2, and 2(1+t squared), with the latter two coinciding at zero parameter. "
                + "The least positive eigenvalue of the action Gram is exactly two and is attained in the z direction. "
                + "Consequently its positive square-root gap is sqrt(2) throughout the whole real family."),
            Theorem("exact_support_gap", "Uniform attained support gap and actual nonzero defects",
                Seq(Call("outputSupport",V("t")),Eq,Call("fixedKernel",V("t")),Caret,Grp(V("perp"))),
                "The output support equals the orthogonal complement of the common fixed kernel. "
                + "On that support, the quadratic form of the actual action Gram is at least twice the squared norm, "
                + "with equality at the unit vector z. The label-linear assignment is nonzero for every t because D(t,x,y)=z. "
                + "For every nonzero t the diagonal defect is nonzero at (1+x)/sqrt(2), the unit generator is nonzero, "
                + "and the label kernel differs from the common fixed kernel: the unit lies in the latter but not the former. "
                + "At t=0 all diagonal defects vanish and the unit generator is zero. These are statements about this "
                + "same action and same positive product, without an assumption of label alternation."))));
}
