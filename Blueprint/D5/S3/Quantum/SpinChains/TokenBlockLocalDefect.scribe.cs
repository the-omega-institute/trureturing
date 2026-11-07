using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class TokenBlockLocalDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/TokenBlockLocalDefect.";
    private static readonly Formula M = F.Id("m"), S = F.Id("s"), Rk = F.Id("r"),
        I = F.Id("i"), R = F.Id("R"), V = F.Id("f");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original complex subset carrier splits by actual outside occupied sets, with additive source and predecessor rank equations and coefficient-one block lowering.",
        H("Outside-occupancy coordinates for the local Boolean defect"), Blocks(
            Paragraph(Text("Let Omega=Fin(m)×Fin(s), fix i in Fin(m), and let O_i consist of those vertices whose first coordinate differs from i. Rank(m,s,r) is the type of all r-element subsets of Omega; Space(m,s,r) is its complex counting Euclidean space. PreviousRank consists of subsets T with card(T)+1=r, and PreviousSpace uses the same counting convention. Thus at r=0 the predecessor type is empty, rather than the rank-zero singleton.")),
            Paragraph(Text("Every outside index R is an actual finset of O_i. Fiber(R) consists of inside finsets A with card(R)+card(A)=r. PreviousFiber(R) instead requires card(R)+card(A)+1=r. Invalid source ranks therefore give empty fibers automatically. In particular, an outside set of cardinality greater than r does not acquire a spurious rank-zero state through truncated subtraction. Distinct outside sets of the same size remain distinct summands.")),
            Node("siteSplit", "The original vertex partition", SiteSplit()),
            Node("rankSplit", "All occupied subsets", RankSplit(false)),
            Node("previousSplit", "All predecessor subsets", RankSplit(true)),
            Node("split", "The counting isometry", Split(false)),
            Node("previousCountingSplit", "The predecessor counting isometry", Split(true)),
            Node("lower", "The physical coefficient-one lowering map", Lower()),
            Node("number", "The physical block number", Number()),
            Node("defect", "The physical local defect", Defect()),
            Node("rankPermutation", "The actual block permutation", Permutation()),
            Node("permutationAction", "The inverse pullback action", Action()),
            Node("invariantSubspace", "The independently defined fixed subspace", Invariants()),
            Node("projection", "The invariant orthogonal projection", Params(Eq(Call("projection",M,S,Rk,I),
                Call("starProjection",Call("invariantSubspace",M,S,Rk,I))))),
            Paragraph(Text("For a permutation pi of Fin(s), rankPermutation maps each occupied subset by prodExtendRight(i,pi): it sends (i,a) to (i,pi(a)) and fixes every outside vertex. permutationAction is the counting linear isometry obtained by pulling coefficients back along the inverse of that subset permutation. invariantSubspace is the fixed subspace of all these actions, and projection is its orthogonal starProjection. This definition imposes no invariance hypothesis on f and uses no averaging formula.")),
            Paragraph(Text("The inverse subset map sends (R,A) to the disjoint union of the outside inclusion of R and {(i,a):a in A}. No coefficient or norm is rescaled. Hence the inner product of f and g is the sum, over all actual R, of the counting inner products of their restrictions; the same identity holds for squared norms. The predecessor decomposition includes the fibers card(R)+s+1=r even though they have no source states. A coefficient-one lowering map must have zero output on these fibers.")),
            Paragraph(Text("The intended local estimate on the complete carrier is s‖f−P_i f‖²≤Re⟨f,D_i f⟩. Here P_i is independently the orthogonal projection onto the vectors fixed by every permutation of block i. In these coordinates a block permutation fixes R and permutes A. Equal-cardinality subset transitivity makes its invariant vectors precisely the functions constant in A separately for each R. Orthogonality to the zero-sum functions identifies P_i with the counting average on each nonempty fiber.")),
            Paragraph(Text("For q=r−card(R) with card(R)≤r and q≤s, the fiber is exactly NativeJohnsonCoercivity.Rank(s,q). Insertion inside the block preserves R, so the physical lowering restricted to this fiber is NativeJohnsonCoercivity.lower(s,q), including its coefficient one. Counting inner products determine the corresponding adjoint. The block number is q on this fiber; consequently the physical defect restricts to NativeJohnsonCoercivity.defect(s,q). NativeJohnsonCoercivity.result then supplies the local estimate on that fiber. Summing uses the same f in every restriction and introduces no probability weights or binomial factors.")),
            Paragraph(Text("A complete identification also requires the equality with the Johnson Laplacian and the sum of I minus each unordered block transposition. The subset partition and physical definitions alone do not establish those identities, the projection identity, or the physical estimate. They do not assert complement covariance, the token-adjacency expansion, global occupancy and norm accounting, tensor spectral positivity, or the variational conclusions. The local objects use no graph, parity, unit-norm, factorization or input-symmetry hypothesis.")))));

    private static DocumentBlock Node(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create("token-block-local-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("All subtype proof fields are suppressed; the additive cardinality predicates are part of the displayed carriers."))),
            DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] xs) =>
        xs.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. xs]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula At(Formula a, Formula b) => new Formula.Apply(a, [b]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(x, Colon, Sp, type)), Comma, Sp, Par(body));
    private static Formula Params(Formula body) =>
        All(M, Call("Nat"), All(S, Call("Nat"), All(Rk, Call("Nat"), All(I, Call("Fin", M), body))));
    private static Formula Space(bool previous) => Call(previous ? "PreviousSpace" : "Space", M,S,Rk);
    private static Formula SiteSplit() => All(M, Call("Nat"), All(S, Call("Nat"),
        All(I, Call("Fin", M), Seq(Call("siteSplit", M,S,I), Colon, Sp,
        Call("Equiv",Call("SumType",Call("Outside", M,S,I),Call("Fin", S)),Call("Sites", M,S)))));
    private static Formula RankSplit(bool previous) => Params(Seq(Call(previous ? "previousSplit" : "rankSplit", M,S,Rk,I),
        Colon, Sp, Call("Equiv",Call(previous ? "PreviousRank" : "Rank", M,S,Rk),
        Call("Sigma",Call("Finset",Call("Outside",M,S,I)),
            Seq(R,Mapsto,Call(previous ? "PreviousFiber" : "Fiber", M,S,Rk,I,R))))));
    private static Formula Split(bool previous) => Params(Seq(Call(previous ? "previousCountingSplit" : "split", M,S,Rk,I),
        Colon, Sp, Call("LinearIsometryEquivC",Space(previous),
        Call("PiLp", D(2), Seq(R, Mapsto, Call(previous ? "PreviousFiberSpace" : "FiberSpace", M,S,Rk,I,R))))));
    private static Formula Permutation() => Params(All(F.Id("pi"),Call("Perm",Call("Fin",S)),
        Seq(Call("rankPermutation",M,S,Rk,I,F.Id("pi")),Colon,Sp,Call("Perm",Call("Rank",M,S,Rk)))));
    private static Formula Action() => Params(All(F.Id("pi"),Call("Perm",Call("Fin",S)),
        Seq(Call("permutationAction",M,S,Rk,I,F.Id("pi")),Colon,Sp,
            Call("LinearIsometryEquivC",Space(false),Space(false)))));
    private static Formula Invariants() => Params(Eq(Call("invariantSubspace",M,S,Rk,I),
        Seq(OpenBrace,V,Colon,Sp,Space(false),Sp,Mid,Sp,All(F.Id("pi"),Call("Perm",Call("Fin",S)),
            Eq(Call("permutationAction",M,S,Rk,I,F.Id("pi"),V),V)),CloseBrace)));
    private static Formula Lower()
    {
        var t=F.Id("T"); var a=F.Id("a");
        var occupied = new Formula.Relation(Par(Seq(I,Comma,a)), FormulaRelationOperator.MemberOf, t);
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(a, Colon, Call("Fin",S))), Sp,
            Call("ite", occupied, D(0), At(V, Call("insert", Par(Seq(I,Comma,a)), t))));
        return Params(All(V, Space(false), All(t, Call("PreviousRank",M,S,Rk),
            Eq(At(Call("lower",M,S,Rk,I,V),t),sum))));
    }
    private static Formula Number()
    {
        var t=F.Id("T");
        return Params(All(V, Space(false), All(t,Call("Rank",M,S,Rk),
            Eq(At(Call("number",M,S,Rk,I,V),t), Mul(Call("ofNatC",Call("card",Call("filterBlock",I,t))),At(V,t))))));
    }
    private static Formula Defect()
    {
        var n=Call("number",M,S,Rk,I); var l=Call("lower",M,S,Rk,I);
        var ident=Call("Id",Space(false));
        return Params(Eq(Call("defect",M,S,Rk,I),
            Sub(Call("comp",n,Sub(Mul(Add(Call("ofNatC",S),D(1)),ident),n)),Call("comp",Call("adjoint",l),l))));
    }
}
