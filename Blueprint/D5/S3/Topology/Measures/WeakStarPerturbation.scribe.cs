using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class WeakStarPerturbationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/WeakStarPerturbation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string s, Formula t) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula And(params Formula[] a)
    {
        var r = new Formula[a.Length * 2 - 1];
        for (var i = 0; i < a.Length; ++i) { r[2 * i] = a[i]; if (i > 0) r[2 * i - 1] = Seq(Sp, Land, Sp); }
        return Seq(r);
    }
    private static Formula At(string s, Formula a) => Call(s, a);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, F.Le, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula N(Formula a) => Call("norm", a);
    private static Formula Strong(Formula a) => Call("toStrongDual", a);
    private static Formula Dual => Call("WeakDual", V("Real"), V("X"));
    private static Formula Space => Seq(All("X", V("Type")),
        OpenBracket, Call("NormedAddCommGroup", V("X")), CloseBracket, Sp,
        OpenBracket, Call("NormedSpace", V("Real"), V("X")), CloseBracket, Sp);
    private static Formula DenseData => Seq(Space, All("A", V("Type")), All("T", V("Type")),
        OpenBracket, Call("TopologicalSpace", V("T")), CloseBracket, Sp,
        All("i", Fn(V("A"), V("T"))), All("f", Fn(V("T"), Dual)), All("g", Fn(V("T"), Dual)));
    private static Formula Diff(Formula p) => N(Strong(Sub(At("f", p), At("g", p))));
    private static Formula Small => Seq(All("a", V("A")), Le(Diff(At("i", V("a"))), V("epsilon")));
    private static Formula DenseBound => Disp(Seq(DenseData, All("epsilon", V("Real")),
        Imp(And(Call("DenseRange", V("i")), Call("Continuous", V("f")), Call("Continuous", V("g")), Small),
            Seq(All("p", V("T")), Le(Diff(V("p")), V("epsilon"))))));
    private static Formula Injection()
    {
        var gap = Seq(All("p", V("T")), All("q", V("T")),
            Imp(Seq(V("p"), Sp, Neq, Sp, V("q")),
                Le(V("c"), N(Strong(Sub(At("f", V("p")), At("f", V("q"))))))));
        var conditions = And(Call("DenseRange", V("i")), Call("Continuous", V("f")),
            Call("Continuous", V("g")), gap, Lt(Seq(D(2), Sp, Cdot, Sp, V("epsilon")), V("c")), Small);
        return Disp(Seq(DenseData, All("c", V("Real")), All("epsilon", V("Real")),
            Imp(conditions, Call("Injective", V("g")))));
    }
    private static Formula Bounded()
    {
        var n = V("n");
        var principal = Seq(All("n", V("Nat")), At("f", Call("pure", n)), Sp, Eq, Sp,
            Call("toWeakDual", At("a", n)));
        var global = Seq(All("p", Call("Ultrafilter", V("Nat"))),
            Le(N(Strong(At("f", V("p")))), V("R")));
        var result = Seq(Ex("f", Fn(Call("Ultrafilter", V("Nat")), Dual)),
            And(Call("Continuous", V("f")), principal, global));
        return Disp(Seq(Space, All("a", Fn(V("Nat"), Call("StrongDual", V("Real"), V("X")))),
            All("R", V("Real")), Imp(Seq(All("n", V("Nat")), Le(N(At("a", n)), V("R"))), result)));
    }
    private static Formula Normalization()
    {
        var n = V("n");
        var an = At("a", n);
        var norms = Seq(n, Sp, Mapsto, Sp, N(an));
        var difference = Seq(n, Sp, Mapsto, Sp,
            Sub(Call("smul", Call("inv", N(an)), an), Call("smul", Call("inv", V("r")), an)));
        var conditions = And(Seq(All("n", V("Nat")), Le(N(an), V("B"))), Lt(D(0), V("r")),
            Call("Tendsto", norms, V("atTop"), Call("nhds", V("r"))));
        return Disp(Seq(All("E", V("Type")),
            OpenBracket, Call("NormedAddCommGroup", V("E")), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", V("Real"), V("E")), CloseBracket, Sp,
            All("a", Fn(V("Nat"), V("E"))), All("B", V("Real")), All("r", V("Real")),
            Imp(conditions, Call("Tendsto", difference, V("atTop"), Call("nhds", D(0))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak-star closed norm balls transfer dense uniform estimates to the entire compactification.",
        H("Uniform weak-star perturbations"),
        Blocks(
            Describe.Lean(DescribeId.Create("dense-uniform-norm-bound"), DeclarationHandle.Create(Owner + "norm_sub_le_of_denseRange"),
                H("The estimate at every point"), StatementSource.FromAuthor(DenseBound), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "X is any real normed space; A is any index type and T any topological space. The image of i is dense. "
                    + "For weak-star continuous f and g, the strong-dual norm of f minus g is at most epsilon everywhere if it is at most epsilon at every i(a). "
                    + "The inverse image of the weak-star closed epsilon ball under f minus g is closed and contains the dense range. No continuity of the norm is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-injection-preservation"), DeclarationHandle.Create(Owner + "injective_of_approximation"),
                H("Injection survives when twice the error is below the gap"), StatementSource.FromAuthor(Injection()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume every unequal pair of f-values has strong-dual norm distance at least c, and twice epsilon is less than c. "
                    + "The dense estimate transfers to every p and q. If g(p)=g(q), the triangle inequality gives norm(f(p)-f(q)) at most twice epsilon, contradicting the gap. "
                    + "The signed-ball application obtains c directly from WeakStarNormSeparation.exists_pos_le_norm_sub on the full Stone–Čech domain."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bounded-dual-stonecech-extension"), DeclarationHandle.Create(Owner + "exists_bounded_extension"),
                H("The bounded extension exists"),
                StatementSource.FromAuthor(Bounded()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Banach–Alaoglu makes the full radius R dual ball compact in the weak-star topology. Extend the sequence into that actual compact subtype and then forget the subtype. "
                    + "The extension agrees at every principal ultrafilter and remains in the same ball at every free ultrafilter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("varying-norm-normalization-correction"), DeclarationHandle.Create(Owner + "normalize_sub_tendsto_zero"),
                H("Normalize by the actual norms"),
                StatementSource.FromAuthor(Normalization()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a bounded sequence a(n) in an arbitrary real normed space with norms tending to r greater than zero, the displayed difference is "
                    + "norm(a(n)) inverse times a(n), minus r inverse times a(n). It tends to zero in norm. "
                    + "The scalar coefficient norm(a(n)) inverse minus r inverse tends to zero; multiplying its norm by the fixed bound B gives a vanishing upper bound. "
                    + "No equality of the raw norms is assumed."))), DescribeRole.Theorem))));
}
