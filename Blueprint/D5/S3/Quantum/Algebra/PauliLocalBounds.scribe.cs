using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliLocalBoundsDocument : IScribeDocumentDefinition
{
    private static Formula V(string x) => F.Id(x);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Pow(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Abs(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Call(string x, params Formula[] args) =>
        Seq(Operatorname, Grp(V(x)), Open,
            Seq(args.SelectMany((a,i) => i == 0 ? new[] { a } : new[] { Comma,a }).ToArray()), Close);
    private static DocumentBlock Theorem(string name, string heading, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-')),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliLocalBounds." + name),
            H(heading), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same real Pauli perturbation has attained sharp local norms and distinct action and label kernels.",
        H("Exact norms, support and spectra of the local Pauli action"),
        Blocks(
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
