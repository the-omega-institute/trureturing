using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TreeParityKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TreeParityKernel.";
    private static readonly Formula Av = F.Id("a"), Bv = F.Id("b"), Dv = F.Id("d"), Mv = F.Id("M");
    private static readonly Formula Tv = F.Id("t"), Iv = F.Id("i"), Hv = F.Id("h"), Nv = F.Id("n");
    private static readonly Formula Uv = F.Id("U"), Vv = F.Id("U_ref"), Ev = F.Id("epsilon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete gap parity record preserves the total variation between the actual and reference tree laws.",
        H("Tree Parity Kernels"),
        Blocks(
            Node("intervals", "Shapes and complete gaps", "intervals",
                Seq(Call("Fiber", Av, Bv), Sp, Cong, Sp,
                    Call("Shapes", Subtract(Nv, D(1))), Sp, Times, Sp, Call("WeakCompositions", Dv, Mv)),
                "For natural a and b with a+b>=1, set n=a+b, k=min(a,b), M=max(a,b), and d=k+1. "
                + "An actual ordered binary tree separates into its ordered shape and the complete gaps between its minority leaves. "
                + "If a<=b, alpha leaves are the separators; otherwise beta leaves are the separators. "
                + "The first and last gaps are included. The d nonnegative gap sizes sum to M. "
                + "The leaf-position subset corresponds to a positive composition of n+1 into d blocks; "
                + "subtracting one from every block gives the gap sizes. Adding one reverses this operation. "
                + "All ordered shapes with n-1 internal nodes are retained.", DescribeRole.Definition),
            Node("parity", "Complete gap parity record", "ξ",
                Equal(Call("xi", Tv, Iv), Call("decide", Equal(Call("mod", Index(F.Id("r"), Iv), D(2)), D(1)))),
                "The Boolean vector has one coordinate for every gap, including both outside gaps. "
                + "Its occupied-coordinate count h is the sum of the Boolean digits. Its terminal parity is M mod 2.",
                DescribeRole.Definition),
            Node("reference", "Reference tree mass", "referenceTreeMass",
                Equal(Call("U_ref", Tv), Ratio(Call("Q", Dv, Mv, Call("xi", Tv)),
                    Multiply(Call("catalan", Subtract(Nv, D(1))),
                        Call("choose", Subtract(Add(Ratio(Subtract(Mv, Hv), D(2)), Dv), D(1)), Subtract(Dv, D(1)))))),
                "The actual tree law U is the uniform mass on Fiber(a,b). The reference mass uses the "
                + "conditioned Bernoulli parity law Q and the actual uniform conditional law given the complete gap parity. "
                + "For a legal parity vector, the denominator is the number of actual trees with that record: "
                + "catalan(n-1) times choose((M-h)/2+d-1,d-1). The parity vector of an actual tree is always legal.",
                DescribeRole.Definition),
            Node("result", "Equal distance and two-sided event bounds", "result", ResultFormula(),
                "For every natural composition a,b with a+b>=1 and M>=d, the parity pushforward of U equals R(d,M). "
                + "The reference mass is nonnegative, sums to one, and its parity pushforward equals Q(d,M). "
                + "The total variation of the two tree laws equals that of R and Q. "
                + "When d>=2 and M>=3d, every event A in the actual composition fiber satisfies "
                + "max(0,U_ref(A)-epsilon)<=U(A)<=min(1,U_ref(A)+epsilon), where "
                + "epsilon=min(1,5(sqrt(d)/M+d(d-1)/M^2)). For d=1 the actual and reference tree laws coincide. "
                + "The shape-gap equivalence reduces parity-fiber counting to the coordinatewise bijection r_i=2t_i+xi_i. "
                + "The resulting fiber count normalizes a common uniform conditional kernel. Summing the absolute "
                + "mass difference within each fiber gives the exact distance identity. The finite parity bound "
                + "and the event characterization of total variation give both event inequalities.", DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        Formula pushU = Equal(Call("pushforward", F.Id("xi"), Uv), Call("R", Dv, Mv));
        Formula posV = Seq(Forall, Sp, Tv, Comma, Sp, Relation(D(0), Leq, Call("U_ref", Tv)));
        Formula massV = Equal(Seq(Index(Sum, Tv), Sp, Call("U_ref", Tv)), D(1));
        Formula pushV = Equal(Call("pushforward", F.Id("xi"), Vv), Call("Q", Dv, Mv));
        Formula tv = Equal(Call("totalVariation", Uv, Vv),
            Call("totalVariation", Call("R", Dv, Mv), Call("Q", Dv, Mv)));
        Formula events = Seq(Paren(And(Relation(D(2), Leq, Dv), Relation(Multiply(D(3), Dv), Leq, Mv))),
            Sp, Rightarrow, Sp, Forall, Sp, F.Id("A"), Comma, Sp,
            And(Relation(Call("max", D(0), Subtract(Call("U_ref", F.Id("A")), Ev)), Leq, Call("U", F.Id("A"))),
                Relation(Call("U", F.Id("A")), Leq, Call("min", D(1), Add(Call("U_ref", F.Id("A")), Ev)))));
        Formula one = Seq(Equal(Dv, D(1)), Sp, Rightarrow, Sp, Equal(Uv, Vv));
        return Seq(Forall, Sp, Av, Comma, Bv, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Paren(And(Relation(D(1), Leq, Add(Av, Bv)), Relation(Dv, Leq, Mv))), Sp, Rightarrow, Sp,
            And(pushU, And(posV, And(massV, And(pushV, And(tv, And(events, one)))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(DescribeId.Create("tree-parity-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Relation(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Paren(a), Sp, Land, Sp, Paren(b));
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Index(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
}
