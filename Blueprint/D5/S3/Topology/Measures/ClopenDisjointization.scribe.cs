using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class ClopenDisjointizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/ClopenDisjointization.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Ex(string name, Formula type) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name) =>
        Seq(OpenBracket, Call(name, V("K")), CloseBracket, Sp);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula And(params Formula[] parts)
    {
        var items = new Formula[parts.Length * 2 - 1];
        for (var i = 0; i < parts.Length; i++)
        {
            items[2 * i] = parts[i];
            if (i > 0) items[2 * i - 1] = Seq(Sp, Land, Sp);
        }
        return Seq(items);
    }
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Num(int n) => D((byte)n);
    private static Formula Quot(Formula a, Formula b) => Seq(F.Frac, Grp(a), Grp(b));
    private static Formula At(string f, Formula x) => Call(f, x);
    private static Formula SetK => Call("Set", V("K"));
    private static Formula SeqOf(Formula type) => Arrow(V("Nat"), type);
    private static Formula Measure => Call("Measure", V("K"));
    private static Formula Signed => Call("SignedMeasure", V("K"));
    private static Formula TV(Formula v) => Call("totalVariation", v);
    private static Formula Mass(Formula measure, Formula set) => Call("real", measure, set);
    private static Formula Whole => Call("univ", V("K"));
    private static Formula Compl(Formula set) => Call("compl", set);
    private static Formula Smul(Formula s, Formula v) => Call("smul", s, v);
    private static Formula Space() => Seq(
        All("K", Seq(V("Type"), Underscore, Grp(V("u")))),
        Inst("TopologicalSpace"), Inst("CompactSpace"), Inst("T2Space"),
        Inst("MeasurableSpace"), Inst("BorelSpace"), Inst("ZeroDimensionalSpace"));

    private static Formula Positive() => Disp(new Formula.Aligned([
        Space(),
        All("mu", SeqOf(Call("ProbabilityMeasure", V("K")))),
        Seq(Open, All("a", V("Nat")), Call("Regular", At("mu", V("a"))), Close, Sp, Rightarrow),
        All("E", SeqOf(SetK)),
        Seq(Open, All("a", V("Nat")), Call("MeasurableSet", At("E", V("a"))), Close, Sp, Rightarrow),
        Seq(Call("PairwiseDisjoint", V("E")), Sp, Rightarrow),
        Seq(Open, All("a", V("Nat")), Eq(Call("apply", At("mu", V("a")), At("E", V("a"))), Num(1)), Close, Sp, Rightarrow),
        Seq(All("eta", V("Real")), Lt(Num(0), V("eta")), Sp, Rightarrow,
            Sp, Lt(V("eta"), Num(1)), Sp, Rightarrow),
        Seq(Ex("n", SeqOf(V("Nat"))), Ex("W", SeqOf(SetK))),
        And(Call("StrictMono", V("n")), Call("PairwiseDisjoint", V("W")),
            Seq(All("k", V("Nat")), And(Call("IsClopen", At("W", V("k"))),
                Call("Nonempty", At("W", V("k"))),
                Lt(Sub(Num(1), Quot(V("eta"), Num(2))),
                    Mass(At("mu", At("n", V("k"))), At("W", V("k")))))))
    ]));

    private static Formula SignedStatement()
    {
        var k = V("k");
        var vk = At("v", At("n", k));
        var wk = At("W", k);
        var tk = At("t", k);
        var qk = Mass(TV(vk), wk);
        var error = Mass(TV(Sub(tk, vk)), Whole);
        var jk = At("j", k);
        var vj = At("v", At("n", jk));
        var tj = At("t", jk);
        var qj = Mass(TV(vj), At("W", jk));
        return Disp(new Formula.Aligned([
            Space(),
            All("v", SeqOf(Signed)),
            Seq(Open, All("a", V("Nat")), Call("Regular", TV(At("v", V("a")))), Close, Sp, Rightarrow),
            Seq(Open, All("a", V("Nat")), Eq(Mass(TV(At("v", V("a"))), Whole), Num(1)), Close, Sp, Rightarrow),
            All("E", SeqOf(SetK)),
            Seq(Open, All("a", V("Nat")), Call("MeasurableSet", At("E", V("a"))), Close, Sp, Rightarrow),
            Seq(Call("PairwiseDisjoint", V("E")), Sp, Rightarrow),
            Seq(Open, All("a", V("Nat")), Eq(Call("apply", TV(At("v", V("a"))), Compl(At("E", V("a")))), Num(0)), Close, Sp, Rightarrow),
            Seq(All("eta", V("Real")), Lt(Num(0), V("eta")), Sp, Rightarrow,
                Sp, Lt(V("eta"), Num(1)), Sp, Rightarrow),
            Seq(Ex("n", SeqOf(V("Nat"))), Ex("W", SeqOf(SetK)), Ex("t", SeqOf(Signed))),
            And(Call("StrictMono", V("n")), Call("PairwiseDisjoint", V("W"))),
            Seq(Land, Sp, Open, All("k", V("Nat")), And(
                Call("IsClopen", wk), Call("Nonempty", wk), Lt(Sub(Num(1), V("eta")), qk), Lt(Num(0), qk), Le(qk, Num(1)),
                Eq(tk, Smul(Call("inv", qk), Call("restrict", vk, wk))),
                Call("Regular", TV(tk)), Eq(Mass(TV(tk), Whole), Num(1)),
                Eq(Call("apply", TV(tk), Compl(wk)), Num(0)),
                Eq(error, Mul(Num(2), Sub(Num(1), qk))), Lt(error, Mul(Num(2), V("eta")))), Close),
            Seq(Land, Sp, Ex("s", V("Real")), Ex("j", SeqOf(V("Nat"))),
                And(Seq(Open, Eq(V("s"), Num(1)), Sp, Lor, Sp, Eq(V("s"), Seq(Minus, Num(1))), Close),
                    Call("StrictMono", V("j")), Call("StrictMono", Call("comp", V("n"), V("j"))),
                    Seq(All("k", V("Nat")), And(
                        Eq(TV(Smul(V("s"), tj)), TV(tj)),
                        Eq(TV(Smul(V("s"), vj)), TV(vj)),
                        Le(Quot(Num(1), Num(2)), Mass(Call("posPart", Call("toJordanDecomposition", Smul(V("s"), tj))), Whole)),
                        Eq(Mass(TV(Sub(Smul(V("s"), tj), Smul(V("s"), vj))), Whole),
                            Mul(Num(2), Sub(Num(1), qj)))))))
        ]));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonmetric finite-history clopen selection and paired-sign signed normalization.",
        H("Clopen disjointization"),
        Blocks(
            Paragraph(Text("K is an arbitrary compact Hausdorff zero-dimensional Borel space. "
                + "Regularity is required for the actual input probabilities or total variations; it is not inferred for arbitrary Borel measures. "
                + "The construction uses classical choice, a free ultrafilter and positive RMK. It makes no effective or choice-free claim.")),
            Describe.Lean(DescribeId.Create("exists-clopen-disjointization"),
                DeclarationHandle.Create(Owner + "exists_clopen_disjointization"),
                H("Disjoint clopens retaining probability mass"), StatementSource.FromAuthor(Positive()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Compactness of ProbabilityMeasure K gives a free-ultrafilter cluster nu. "
                        + "Positive RMK represents integration against nu by a regular lambda. Finiteness follows from regularity on compact K before evaluating one to prove lambda(K)=1. "
                        + "The representing identity tests every fixed clopen indicator; it does not identify nu and lambda on all Borel sets.")),
                    Paragraph(Text("Countable additivity makes lambda(E_n) summable and hence convergent to zero. "
                        + "The recursive state contains the next allowed index and the actual preceding clopen union P, with lambda.real(P)<eta/8. "
                        + "Set delta=(eta/8-lambda.real(P))/2. Intersect the ultrafilter-large fixed-P test mu_n(P)<eta/4, the eventual bound lambda(E_n)<delta, and the increasing-index tail. "
                        + "Regularity of the selected input supplies a compact core inside E_n minus P with mass greater than 1-eta/2. "
                        + "Outer regularity of lambda and the zero-dimensional clopen sandwich give a clopen W containing that core, avoiding all of P and of lambda mass below delta. "
                        + "The new union remains below eta/8, so ordinary recursion yields increasing indices and actual pairwise disjoint nonempty clopens. "
                        + "No countable filter intersection, moving-Borel convergence, metrizability or sequential compactness is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-signed-clopen-disjointization"),
                DeclarationHandle.Create(Owner + "exists_signed_clopen_disjointization"),
                H("Total-variation normalization and one paired common sign"),
                StatementSource.FromAuthor(SignedStatement()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Apply the positive construction to the actual regular total variations. "
                        + "For q=totalVariation(v)(W)>0, define t=q inverse times the restriction of v to W. "
                        + "The variation/restriction and variation/scalar interfaces are required: signed mass v(W), which may vanish by cancellation, is not the normalization factor. "
                        + "Regularity survives measurable restriction and finite positive rescaling. The normalized measure has total variation one and zero total variation on the complement of W.")),
                    Paragraph(Text("Restrict t-v separately to W and its complement. Their variations have masses (q inverse minus one)q and 1-q. "
                        + "Additivity of the variation measure gives the exact error 2(1-q), including q=1. "
                        + "An infinite pigeonhole argument selects one sign and a further increasing subsequence with positive Jordan mass at least one half. "
                        + "The same sign multiplies BOTH the approximant and the corresponding original, preserving the exact error. "
                        + "A fixed positive approximation bound supplies no weak-star convergence of t; the theorem asserts none."))), DescribeRole.Theorem),
            Paragraph(Text("The ordinary selection argument is classical background, not a novelty claim. "
                + "The source-level suppliers are the pinned Mathlib Prokhorov forward compactness theorem, positive RealRMK, finite-measure summability, regularity, the clopen sandwich, and the signed/Jordan variation interfaces. "
                + "Library/Topology/kania2026talagrand.md records the application boundary. "
                + "Neither local theorem proves KPR, the signed A-G recursion, final capture, the Grothendieck C(T) endpoint or exclusion in the whole signed dual unit ball. "
                + "Information audit remains unfinished: full raw telescope reconstruction/sourceSelection and dependent-family realization, variation and sensitivity evidence are absent. "
                + "The existing source-reconstruction issue is https://github.com/the-omega-institute/trureturing/issues/16293. No validated registration or kernel acceptance is asserted by this document.")))));
}
