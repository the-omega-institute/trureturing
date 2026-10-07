using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TreeParityKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TreeParityKernel.";
    private static readonly LibraryNoteRef StarsAndBars =
        LibraryNoteRef.Create("D5/L/TotalVariation/mathlib2026starsbars");
    private static readonly LibraryNoteRef BernoulliParity =
        LibraryNoteRef.Create("D5/L/TotalVariation/siegrist2026generating");
    private static readonly Formula Av = F.Id("a"), Bv = F.Id("b"), Dv = F.Id("d"), Mv = F.Id("M");
    private static readonly Formula Tv = F.Id("t"), Iv = F.Id("i"), Hv = F.Id("h"), Nv = F.Id("n");
    private static readonly Formula Uv = F.Id("U"), Vv = F.Id("V"), Ev = F.Id("epsilon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete gap parity record preserves the total variation between the actual and reference tree laws.",
        H("Tree Parity Kernels"),
        Blocks(
            Node("actual", "Composition parity mass", "R", ActualFormula(),
                "The parameters d and M are natural numbers, xi : Fin d -> Bool, and h is the number of true coordinates of xi. "
                + "The guard requires h <= M and h mod 2 = M mod 2. The mass is zero when either test fails; "
                + "the binomial coefficient in the nonzero branch is evaluated only for the resulting natural parameters. "
                + "Its numerator counts the weak compositions of M into d parts with parity vector xi.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(StarsAndBars)),
            Node("reference-law", "Conditioned Bernoulli mass", "Q", ReferenceFormula(),
                "Here nu = M/(2M+d), eta = d/(2M+d), and p_e = (1+(-1)^M eta^d)/2. "
                + "The mass is zero when h mod 2 differs from M mod 2. For positive d and M, "
                + "this formula describes independent Bernoulli(nu) bits conditioned on the terminal parity. "
                + "The conditioned bits are not asserted to be independent. Both masses have exactly the form "
                + "used by the finite parity bound.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(BernoulliParity)),
            Node("intervals", "Shapes and complete gaps", "intervals",
                Seq(Call("Fiber", Av, Bv), Sp, Sim, Sp,
                    Call("Shapes", Subtract(Nv, D(1))), Sp, Times, Sp, Call("WeakCompositions", Dv, Mv)),
                "For natural a and b with a+b>=1, set n=a+b, k=min(a,b), M=max(a,b), and d=k+1. "
                + "An actual ordered binary tree separates into its ordered shape and the complete gaps between its minority leaves. "
                + "If a<=b, alpha leaves are the separators; otherwise beta leaves are the separators. "
                + "The first and last gaps are included. The d nonnegative gap sizes sum to M. "
                + "The separator positions, read left to right, correspond to a positive composition of n+1 into d blocks; "
                + "subtracting one from every block gives the gap sizes, a weak composition of M into d parts. "
                + "Adding one reverses this operation. "
                + "All ordered shapes with n-1 internal nodes are retained.", DescribeRole.Definition,
                AssessedProvenance.FromRepo()),
            Node("parity", "Complete gap parity record", "gapParity",
                Equal(Call("xi", Tv, Iv), Call("decide", Equal(Call("mod", Index(F.Id("r"), Iv), D(2)), D(1)))),
                "The Boolean vector has one coordinate for every gap, including both outside gaps. "
                + "Its occupied-coordinate count h is the number of true coordinates, and h mod 2 equals M mod 2.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("reference", "Reference tree mass", "referenceTreeMass",
                Equal(Call("V", Tv), Ratio(Call("Q", Dv, Mv, Call("xi", Tv)),
                    Multiply(Call("catalan", Subtract(Nv, D(1))),
                        Call("choose", Subtract(Add(Ratio(Subtract(Mv, Hv), D(2)), Dv), D(1)), Subtract(Dv, D(1)))))),
                "The actual tree law U is the uniform mass on Fiber(a,b). The reference mass uses the "
                + "conditioned Bernoulli parity law Q and the actual uniform conditional law given the complete gap parity. "
                + "For a legal parity vector, the denominator is the number of actual trees with that record: "
                + "catalan(n-1) times choose((M-h)/2+d-1,d-1). The parity vector of an actual tree is always legal.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(StarsAndBars, BernoulliParity)),
            Node("result", "Equal distance and two-sided event bounds", "result", ResultFormula(),
                "For every natural composition a,b with a+b>=1 and M>=d, the parity pushforward of U equals R(d,M). "
                + "The reference mass is nonnegative, sums to one, and its parity pushforward equals Q(d,M). "
                + "The total variation of the two tree laws equals that of R and Q. "
                + "When d>=2 and M>=3d, every event A in the actual composition fiber satisfies "
                + "max(0,V(A)-epsilon)<=U(A)<=min(1,V(A)+epsilon), where "
                + "epsilon=min(1,5(sqrt(d)/M+d(d-1)/M^2)). For d=1 the actual and reference tree laws coincide. "
                + "The shape-gap equivalence and the prescribed-parity weak-composition count give, for every legal "
                + "parity vector xi, exactly catalan(n-1) times choose((M-h)/2+d-1,d-1) actual trees with record xi, "
                + "and none for an illegal vector. This fiber count normalizes a common uniform conditional kernel. "
                + "Within each parity fiber the two tree laws differ by one sign, so the deterministic parity channel "
                + "preserves their total variation. The finite parity bound and the event characterization of total "
                + "variation give both event inequalities. For d=1 the single gap has the parity of M, the two parity "
                + "masses agree, and so the tree laws agree.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(StarsAndBars, BernoulliParity)))));

    private static Formula ResultFormula()
    {
        Formula pushU = Equal(Call("pushforward", F.Id("xi"), Uv), Call("R", Dv, Mv));
        Formula posV = Seq(Forall, Sp, Tv, Comma, Sp, Relation(D(0), Leq, Call("V", Tv)));
        Formula massV = Equal(Seq(Index(Sum, Tv), Sp, Call("V", Tv)), D(1));
        Formula pushV = Equal(Call("pushforward", F.Id("xi"), Vv), Call("Q", Dv, Mv));
        Formula tv = Equal(Call("totalVariation", Uv, Vv),
            Call("totalVariation", Call("R", Dv, Mv), Call("Q", Dv, Mv)));
        Formula events = Seq(Paren(And(Relation(D(2), Leq, Dv), Relation(Multiply(D(3), Dv), Leq, Mv))),
            Sp, Rightarrow, Sp, Forall, Sp, F.Id("A"), Comma, Sp,
            And(Relation(Call("max", D(0), Subtract(Call("V", F.Id("A")), Ev)), Leq, Call("U", F.Id("A"))),
                Relation(Call("U", F.Id("A")), Leq, Call("min", D(1), Add(Call("V", F.Id("A")), Ev)))));
        Formula one = Seq(Equal(Dv, D(1)), Sp, Rightarrow, Sp, Equal(Uv, Vv));
        return Seq(Forall, Sp, Av, Comma, Bv, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Paren(And(Relation(D(1), Leq, Add(Av, Bv)), Relation(Dv, Leq, Mv))), Sp, Rightarrow, Sp,
            And(pushU, And(posV, And(massV, And(pushV, And(tv, And(events, one)))))));
    }

    private static Formula Parity() => Equal(Call("mod", Hv, D(2)), Call("mod", Mv, D(2)));

    private static Formula Closed(Formula body) => Seq(Forall, Sp, Dv, Comma, Mv, Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp, Forall, Sp, F.Xi, Comma, Sp, body);

    private static Formula ActualFormula() => Closed(Equal(Call("R", Dv, Mv, F.Xi),
        Call("ite", And(Relation(Hv, Leq, Mv), Parity()),
            Ratio(Call("choose", Subtract(Add(Ratio(Subtract(Mv, Hv), D(2)), Dv), D(1)), Subtract(Dv, D(1))),
                Call("choose", Subtract(Add(Mv, Dv), D(1)), Subtract(Dv, D(1)))), D(0))));

    private static Formula ReferenceFormula() => Closed(Equal(Call("Q", Dv, Mv, F.Xi),
        Call("ite", Parity(), Ratio(Multiply(Power(F.Nu, Hv),
            Power(Paren(Subtract(D(1), F.Nu)), Subtract(Dv, Hv))), Index(F.Id("p"), F.Id("e"))), D(0))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("tree-parity-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Relation(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Paren(a), Sp, Land, Sp, Paren(b));
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Index(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Power(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
}
