using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedBallReductionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedBallReduction.";
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
    private static Formula At(string s, Formula n) => Call(s, n);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, F.Le, Sp, b);
    private static Formula SeqOf(Formula t) => Fn(V("Nat"), t);
    private static Formula Signed => Call("SignedMeasure", V("K"));
    private static Formula Beta => Call("Ultrafilter", V("Nat"));
    private static Formula Dual => Call("WeakDual", V("Real"), Call("ContinuousMap", V("K"), V("Real")));
    private static Formula TV(Formula a) => Call("totalVariation", a);
    private static Formula Mass(Formula a) => Call("real", TV(a), V("univ"));
    private static Formula Space => Seq(All("K", V("Type")),
        OpenBracket, Call("TopologicalSpace", V("K")), CloseBracket, Sp,
        OpenBracket, Call("CompactSpace", V("K")), CloseBracket, Sp,
        OpenBracket, Call("T2Space", V("K")), CloseBracket, Sp,
        OpenBracket, Call("MeasurableSpace", V("K")), CloseBracket, Sp,
        OpenBracket, Call("BorelSpace", V("K")), CloseBracket, Sp);
    private static Formula Bound(string h) => Seq(All("p", Call("StoneCech", V("Nat"))),
        Le(Call("norm", Call("toStrongDual", At(h, V("p")))), D(1)));
    private static Formula Extension => And(Call("Continuous", V("f")), Call("Injective", V("f")),
        Seq(All("n", V("Nat")), Eq(At("f", Call("pure", V("n"))),
            Call("toWeakDual", Call("signedFunctional", At("b", V("n")))))),
        Seq(All("p", Beta), Le(Call("norm", Call("toStrongDual", At("f", V("p")))), D(1))));
    private static Formula Reduction()
    {
        var n = V("n");
        var bn = At("b", n);
        var carriers = Seq(All("n", V("Nat")),
            Eq(Call("apply", TV(bn), Call("compl", At("E", n))), D(0)));
        var outputs = And(Seq(All("n", V("Nat")), Call("Regular", TV(bn))),
            Seq(All("n", V("Nat")), Eq(Mass(bn), D(1))),
            Seq(All("n", V("Nat")), Call("MeasurableSet", At("E", n))),
            Call("PairwiseDisjoint", V("E")), carriers, Extension);
        var result = Seq(Ex("b", SeqOf(Signed)), Ex("E", SeqOf(Call("Set", V("K")))),
            Ex("f", Fn(Beta, Dual)), outputs);
        return Disp(Seq(Space, All("h", Fn(Call("StoneCech", V("Nat")), Dual)),
            Imp(And(Call("Continuous", V("h")), Call("Injective", V("h")), Bound("h")), result)));
    }

    private static Formula Collision()
    {
        var n = V("n");
        var sn = At("s", n);
        var wn = At("W", n);
        var freeP = Le(Call("toFilter", V("p")), V("cofinite"));
        var freeQ = Le(Call("toFilter", V("q")), V("cofinite"));
        var collision = Seq(Ex("p", Beta), Ex("q", Beta), And(freeP, freeQ,
            Seq(V("p"), Sp, Neq, Sp, V("q")), Eq(At("f", V("p")), At("f", V("q")))));
        var extension = Seq(All("f", Fn(Beta, Dual)),
            Imp(And(Call("Continuous", V("f")), Seq(All("n", V("Nat")),
                Eq(At("f", Call("pure", n)), Call("toWeakDual", Call("signedFunctional", sn))))), collision));
        var assumptions = And(
            Seq(All("n", V("Nat")), Call("Regular", TV(sn))),
            Seq(All("n", V("Nat")), Eq(Mass(sn), D(1))),
            Seq(All("n", V("Nat")), And(Call("IsClopen", wn), Call("Nonempty", wn))),
            Call("PairwiseDisjoint", V("W")),
            Seq(All("n", V("Nat")), Eq(Call("apply", TV(sn), Call("compl", wn)), D(0))),
            Seq(All("n", V("Nat")), Le(Seq(Frac, Grp(D(1)), Grp(D(2))),
                Call("real", Call("posPart", Call("toJordanDecomposition", sn)), V("univ")))));
        return Disp(Seq(Space, Eq(Call("SignedClopenCollision", V("K")),
            Seq(All("s", SeqOf(Signed)), All("W", SeqOf(Call("Set", V("K")))), Imp(assumptions, extension)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From a copy in the full signed dual ball to a normalized disjoint sequence, and from signed clopen collision to nonembedding.",
        H("Complete signed-ball analytic reduction"),
        Blocks(
            Describe.Lean(DescribeId.Create("normalized-signed-disjoint-full-extension"),
                DeclarationHandle.Create(Owner + "exists_normalized_disjoint_embedding"),
                H("KPR normalization and full-domain thinning"), StatementSource.FromAuthor(Reduction()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "K is any compact Hausdorff Borel space, without a metrizability or zero-dimensionality hypothesis. h is an arbitrary weak-star continuous injection of StoneCech Nat into the entire real signed dual unit ball of C(K,Real). "
                        + "The output consists of actual regular signed measures b(n), pairwise disjoint Borel sets E(n) carrying their total variations, and a continuous injective extension f on every ultrafilter. "
                        + "Each b(n) has variation mass one, f(pure n) is its integration functional, and every f(p) has strong-dual norm at most one.")),
                    Paragraph(Text(
                        "Signed Riesz represents the original principal functionals by regular signed measures. The actual raw signed KPR theorem selects literal restrictions u(n) and v(n), with u(n) carried by disjoint Borel sets, "
                        + "v(n) converging against every continuous linear functional on the dual, and norm(u(n)) tending to a nonnegative real r. The selected original extension remains injective because mapping ultrafilters along an injection is injective.")),
                    Paragraph(Text(
                        "At every free ultrafilter, the v extension equals its one weak limit V. Consequently the u extension is the selected original extension minus V. "
                        + "If r were zero, u would tend to zero in norm and the original extension would be constant on the free part. Two distinct free ultrafilters contradict its injection. Thus r is positive, and a tail has strictly positive actual norms.")),
                    Paragraph(Text(
                        "Define b(n)=u(n)/norm(u(n)) on this tail. The regularity, unit norm and literal carrying set follow from scalar total variation and restriction identities. "
                        + "normalize_sub_tendsto_zero controls the norm difference between this sequence and u(n)/r. It vanishes on every free ultrafilter, so the free extension is the selected original extension minus V, divided by r. "
                        + "This proves free/free injection. Disjoint carriers and mass one prove principal/principal injection. CountableAvoidance removes every principal/free collision by an actual increasing subsequence, leaving a full injective extension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-clopen-collision-premise"), DeclarationHandle.Create(Owner + "SignedClopenCollision"),
                H("The analytic collision premise"),
                StatementSource.FromAuthor(Collision()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The predicate quantifies over every natural-number sequence of regular signed measures of variation mass one and every pairwise disjoint sequence of nonempty clopens carrying them. "
                    + "It requires positive Jordan-part mass at least one half for every term. For every weak-star continuous extension of the exact principal integration functionals, "
                    + "it gives two distinct free ultrafilters with equal images. It does not assume nonembedding or any KPR, normalization, approximation or extension supplier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-signed-ball-collision-reduction"),
                DeclarationHandle.Create(Owner + "not_injective_signed_ball_of_collision"), H("Exclusion of the entire signed unit ball"),
                StatementSource.FromAuthor(Disp(Seq(Space,
                    OpenBracket, Call("ZeroDimensionalSpace", V("K")), CloseBracket, Sp,
                    All("h", Fn(Call("StoneCech", V("Nat")), Dual)),
                    Imp(And(Call("SignedClopenCollision", V("K")), Call("Continuous", V("h")), Bound("h")),
                        Seq(Neg, Sp, Call("Injective", V("h"))))))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume K is also zero-dimensional and satisfies SignedClopenCollision. A supposed signed-ball embedding yields the normalized disjoint-Borel sequence above. "
                        + "The existing WeakStarNormSeparation theorem gives one c greater than zero for all unequal points of its entire extension. Choose eta=min(c/16,1/4).")),
                    Paragraph(Text(
                        "The actual exists_signed_clopen_disjointization theorem supplies increasing selections, disjoint nonempty clopens, normalized regular signed restrictions, and a single sign s in {1,-1} after another increasing selection. "
                        + "The entire selected original sequence and the approximants are multiplied by that same sign. Each approximant has positive Jordan mass at least one half, and its variation distance from the corresponding signed original term is less than twice eta.")),
                    Paragraph(Text(
                        "Reindexing and the fixed sign retain the full norm gap c. Banach–Alaoglu supplies the approximant extension. Weak-star closed norm balls transfer the twice-eta bound from every principal point to every ultrafilter. "
                        + "Since four eta is less than c, injective_of_approximation makes that full extension injective. SignedClopenCollision gives two distinct free points with the same value, a contradiction. "
                        + "The collision premise must still be established for the intended CH construction; this analytic reduction does not realize the transfinite construction or assert that the full CH target is solved."))),
                DescribeRole.Theorem))));
}
