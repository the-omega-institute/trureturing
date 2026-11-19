using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class NativeJohnsonCoercivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.";
    private static readonly Formula N = F.Id("N");
    private static readonly Formula R = F.Id("r");
    private static readonly Formula V = F.Id("f");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient-one lowering map on every complex fixed-cardinality space has counting-average coercivity with constant N.",
        H("Counting-average coercivity on native rank spaces"), Blocks(
            Paragraph(Text("For natural N and r, Rank(N,r) consists of the r-element subsets of Fin(N), and PreviousRank(N,r) consists of subsets T satisfying card(T)+1=r. Layer and PreviousLayer are the corresponding complex Euclidean function spaces, with counting inner products. The predecessor carrier is empty when r=0. No parity assumption, enlargement of N, normalization of counting measure, or restriction to real vectors is imposed.")),
            Node("Rank", "The fixed-rank carrier", Rank(false)),
            Node("PreviousRank", "The predecessor carrier", Rank(true)),
            Node("Layer", "The counting Hilbert space", Layer(false)),
            Node("PreviousLayer", "The predecessor counting Hilbert space", Layer(true)),
            Node("lower", "Coefficient-one lowering", Lower()),
            Node("average", "The actual counting average", Average()),
            Node("defect", "The native lowering defect", Defect()),
            Describe.Lean(DescribeId.Create("native-johnson-coercivity-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Coercivity relative to the counting average"),
                StatementSource.FromAuthor(Disp(Result())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For r≤N, card(Rank(N,r))=choose(N,r)>0. The sum of f−average(N,r,f) is zero. Thus average is the orthogonal projection onto the line of constant functions. The defect is r(N−r+1)I−W*W, where W=lower(N,r) and W* is the actual adjoint for the counting inner products. In this scalar coefficient subtraction is in the complex field after casting N and r. The quadratic form equals r(N−r+1)‖f‖²−‖Wf‖².")),
                    Paragraph(Text("The BooleanCollectiveLadders rankConfigurationEquiv identifies these subsets with the original N-bit configurations of occupancy r. Extending a function by zero gives E_r; the same construction on occupancy(x)+1=r gives Eminus_r. Reindexing the counting sums proves both maps preserve inner products and norms. The original site_entry formula gives L(N)E_r=Eminus_r W with every coefficient equal to one. The original adjoint_U identity transports the Boolean quadratic form to the native defect.")),
                    Paragraph(Text("Repeated rank_split, starting from primitive_zero_eq, constructs f=∑_{t=0}^r U(N)^(r−t)v_t with v_t primitive of rank t. primitive_orthogonal and inner_power_orthogonal make different t components orthogonal. primitive_degree and primitive_endpoint kill components with t>N−r. The original primitive_recurrence gives defect eigenvalue t(N+1−t); for the surviving positive t, its difference from N is (t−1)(N−t)≥0.")),
                    Paragraph(Text("Let the vacuum be the all-one bit configuration, the unique configuration of occupancy zero. On a function constant with value c at rank r and zero elsewhere, U has constant value (r+1)c at rank r+1. Induction therefore gives U(N)^r v=r! v(vacuum) on rank r for every primitive rank-zero v. This identifies the zero string with a constant function. Its orthogonality to all remaining strings forces the residual counting sum to vanish, so the zero string is exactly E_r average(N,r,f). Combining this identification with the orthogonal defect estimate proves the displayed inequality.")),
                    Paragraph(Text("The conclusion includes odd and even N, both endpoints r=0 and r=N, and the empty-site extension N=0. At r=0 the lowering target is empty and the rank space is one dimensional. At r=N only the constant string survives. No claim about a graph Hamiltonian, tensor spectators, confinement, or physical realization follows without its separate correspondence."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create("native-johnson-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("All subtype proof fields are suppressed in the displayed notation."))),
            DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(x, Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Ranks(Formula body) => All(N, Nat(), All(R, Nat(), body));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Sum(Formula x, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(x, Sp, InMacro, Sp, type)), Sp, body);
    private static Formula Coefficient() => Mul(Call("ofNatC", R),
        Add(Sub(Call("ofNatC", N), Call("ofNatC", R)), D(1)));
    private static Formula Rank(bool previous)
    {
        var a = F.Id("A");
        return Ranks(Eq(Call(previous ? "PreviousRank" : "Rank", N, R),
            Seq(OpenBrace, a, Colon, Sp, Call("Finset", Call("Fin", N)), Sp, Mid, Sp,
                Eq(previous ? Add(Call("card", a), D(1)) : Call("card", a), R), CloseBrace)));
    }
    private static Formula Layer(bool previous) => Ranks(Eq(Call(previous ? "PreviousLayer" : "Layer", N, R),
        Call("EuclideanSpace", Complex(), Call(previous ? "PreviousRank" : "Rank", N, R))));
    private static Formula Lower()
    {
        var t = F.Id("T"); var i = F.Id("i");
        return Ranks(All(V, Call("Layer", N, R), All(t, Call("PreviousRank", N, R),
            Eq(At(Call("lower", N, R, V), t), Sum(i, Call("Fin", N),
                Call("ite", Mem(i, t), D(0), At(V, Call("insert", i, t))))))));
    }
    private static Formula Average()
    {
        var a = F.Id("A"); var b = F.Id("B");
        return Ranks(All(V, Call("Layer", N, R), All(a, Call("Rank", N, R),
            Eq(At(Call("average", N, R, V), a), Mul(
                new Formula.Fraction(D(1), Call("ofNatC", Call("card", Call("Rank", N, R)))),
                Sum(b, Call("Rank", N, R), At(V, b)))))));
    }
    private static Formula Defect() => Ranks(Eq(Call("defect", N, R), Sub(
        Mul(Coefficient(), Call("id", Call("Layer", N, R))),
        Call("comp", Call("adjoint", Call("lower", N, R)), Call("lower", N, R)))));
    private static Formula Result() => Ranks(Imp(Le(R, N), All(V, Call("Layer", N, R),
        Le(Mul(Call("ofNatR", N), new Formula.Power(Call("norm", Sub(V, Call("average", N, R, V))), D(2))),
            Call("re", Call("innerC", V, Call("defect", N, R, V)))))));
}
