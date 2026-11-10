using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeExtremaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every total integer N >= 3, the actual order-three Gaussian genuine multi-entropy is minimized precisely by the balanced positive integer triples and maximized precisely by permutations of (N-2,1,1), with all ties retained. The two extremal classes coincide at N=3 and N=4.",
        H("All-total integer extrema at replica three"),
        Blocks(
            Paragraph(Text("Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. Camargo and Nishida supply the physical family; Marshall, Olkin and Arnold supply the classical majorization criterion. The proof reuses the actual integral/Fourier bridge and the strict scalar comparison, retaining their canonical and transplant credits. Higher replicas, physical replica-one continuation, other branches and separate fixed-a Page/large-N asymptotics remain outside this result.")),
            Node("balanced", "The balanced representative", "balanced",
                "Write N=3q+r with q=N/3 and r=N%3 in {0,1,2}, and put delta_0=[r>0], delta_1=[r>1]. The descending representative has exactly r entries q+1 and the remaining entries q: (q+delta_0,q+delta_1,q). All permutations represent the same balanced class. In the extrema formulas below, b and e abbreviate b(N) and e(N).", DescribeRole.Definition),
            Node("extreme", "The extreme representative", "extreme",
                "The extreme positive integer representative is (N-2,1,1). Its full permutation class is retained, including the duplicate entries and the fully tied N=3 case.", DescribeRole.Definition),
            Node("is-balanced", "Balanced integer triples", "IsBalanced",
                "A triple is balanced exactly when x_i <= x_j+1 for every ordered pair i,j, equivalently every pair of integer sizes differs by at most one. This definition does not impose an ordering on party labels.", DescribeRole.Definition),
            Node("integer", "Scalar extrema and both iff equality classes", "integer_extrema",
                "For every k>0, integer N>=3 and positive integer triple x of total N, V(k,balanced N) <= V(k,x) <= V(k,N-2,1,1). Equality at the minimum holds if and only if x is balanced; equality at the maximum holds if and only if x is a permutation of (N-2,1,1). The values are the exact logarithmic expression of ReplicaThreeScalar, evaluated at the displayed representatives, for all three residues of N. Sorting supplies the two prefix bounds; the strict Schur theorem supplies both permutation equality directions. This is universal in N, not a finite enumeration.", DescribeRole.Theorem),
            Node("physical", "Actual integral-defined physical extrema", "GM3_three_extrema",
                "For every integer N>=3, a>1 and positive integer labelled triple x with sum N, the actual integral-defined GaussianMultiEntropyAsymptotic.GM3 3 x_0 x_1 x_2 a lies between V(kappa,balanced N) and V(kappa,N-2,1,1), where kappa=3(a^2-1)/(4(N-1)). It equals the lower endpoint if and only if every pair of sizes differs by at most one; it equals the upper endpoint if and only if x is a permutation of (N-2,1,1). Both endpoint representatives are positive triples of the required total, so these bounds are attained. Each endpoint is the exact formula log((1+kappa s)^2/(D_x D_y D_z))/12 evaluated at its representative, with all three labelled cut factors. Physical mode counts are integers; positive reals occur only in the scalar comparison used by the proof. At a=1 the separate physical behavior theorem gives zero and all triples tie.", DescribeRole.Theorem),
            Node("degeneracy", "Coincident extrema at totals three and four", "extremal_degeneracy",
                "For every k>0 and N>=3, the extreme representative is balanced if and only if N=3 or N=4; equivalently the minimum and maximum values coincide if and only if N=3 or N=4. Thus every admissible triple at these totals belongs to the common extremal class, with no false strict separation. For every N>=5 the two extremal values are distinct and the minimum is strictly smaller.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-three-extrema-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Indices => Seq(OpenBrace, D(0), Comma, D(1), Comma, D(2), CloseBrace);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Quotient => Seq(Lfloor, Frac, Grp(F.Id("N")), Grp(D(3)), Rfloor);
    private static Formula Remainder => new Formula.Apply(F.Id("mod"), [F.Id("N"), D(3)]);
    private static Formula Indicator(Formula condition) => Seq(Mathbf, Grp(D(1)), Underscore, Grp(condition));
    private static Formula Call(string f, string x) => Seq(F.Id(f), Open, F.Id(x), Close);
    private static Formula V(string x) => Seq(F.Id("V"), Open, F.Id("k"), Comma, F.Id(x), Close);
    private static Formula GM => Seq(F.Id("GM"), Underscore, D(3), Open, F.Id("x"), Comma, F.Id("a"), Close);
    private static Formula Statement(string declaration) => declaration switch
    {
        "balanced" => All("N", Naturals, Seq(Call("b", "N"), Eq, Open,
            Quotient, Plus, Indicator(Seq(D(0), Lt, Remainder)), Comma,
            Quotient, Plus, Indicator(Seq(D(1), Lt, Remainder)), Comma, Quotient, Close)),
        "extreme" => All("N", Naturals, Seq(Call("e", "N"), Eq, Open,
            F.Id("N"), Minus, D(2), Comma, D(1), Comma, D(1), Close)),
        "IsBalanced" => All("x", Seq(Indices, To, Sp, Naturals), Seq(Call("B", "x"), Sp, Iff, Sp,
            All("i", Indices, All("j", Indices, Seq(F.Id("x"), Underscore, F.Id("i"), Le, Sp,
                F.Id("x"), Underscore, F.Id("j"), Plus, D(1)))))),
        "integer_extrema" => Seq(V("b"), Le, Sp, V("x"), Le, Sp, V("e"), Semi,
            V("x"), Eq, V("b"), Sp, Iff, Sp, Call("B", "x"), Semi,
            V("x"), Eq, V("e"), Sp, Iff, Sp, Exists, Sp, SigmaLower, Comma,
            F.Id("x"), Eq, F.Id("e"), Circ, Sp, SigmaLower),
        "GM3_three_extrema" => Seq(V("b"), Le, Sp, F.Id("GM"), Underscore, D(3), Open, F.Id("x"), Comma,
            F.Id("a"), Close, Le, Sp, V("e"), Semi,
            GM, Eq, V("b"), Sp, Iff, Sp, Call("B", "x"), Semi,
            GM, Eq, V("e"), Sp, Iff, Sp, Exists, Sp, SigmaLower, Comma,
            F.Id("x"), Eq, F.Id("e"), Circ, Sp, SigmaLower, Semi,
            F.Id("k"), Eq, Kappa, Open, F.Id("N"), Comma, F.Id("a"), Close),
        _ => Seq(Call("B", "e"), Sp, Iff, Sp, F.Id("N"), Eq, D(3), Sp, Lor, Sp, F.Id("N"), Eq, D(4), Semi,
            V("b"), Eq, V("e"), Sp, Iff, Sp, F.Id("N"), Eq, D(3), Sp, Lor, Sp, F.Id("N"), Eq, D(4))
    };
}
