using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class CompactPseudoOrbitSelectorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(V(name))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula AllTyped(string s, Formula t) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp);
    private static Formula AllIn(string s, Formula t) => Seq(Forall, Sp, V(s), InMacro, Sp, t, Comma, Sp);
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula AllEps => Seq(AllIn("eps", R), V("eps"), Gt, Sp, Num(0), Rightarrow);
    private static Formula P(string scale) => Call("Space", V("f"), V(scale));
    private static Formula Inst(string name) => Seq(OpenBracket, Call(name, V("M")), CloseBracket);
    private static Formula Hyp(Formula f) => Seq(Open, f, Close, Sp, Rightarrow);
    private static Formula E(Formula i) => Call("e", V("x"), i);
    private static Formula D(Formula k) => Call("dist", Call("orbit", V("f"), Call("Q", V("x")), k), Call("x", k));
    private static Formula RestrictedD(Formula k) => Call("dist", Call("orbit", V("f"),
        Call("Q", Call("inclusion", V("gamma"), V("delta"), V("x"))), k), Call("x", k));
    private static Formula[] Selector(bool positive = false) => [
        Seq(AllTyped("M", V("Type")), Inst("MetricSpace"), Sp, Inst("CompactSpace")),
        Seq(AllTyped("f", Call("Homeomorph", V("M"), V("M"))), AllIn("delta", R)),
        Hyp(Seq(Num(0), positive ? Lt : Le, Sp, V("delta"))),
        AllTyped("Q", Seq(P("delta"), To, Sp, V("M"))),
        Hyp(Call("Continuous", V("Q"))),
        Hyp(Seq(AllIn("p", V("M")),
            Call("Q", Call("trueOrbit", V("f"), V("delta"), V("p"))), Eq, Sp, V("p"))) ];
    private static Formula Equivariance => Hyp(Seq(AllIn("x", P("delta")),
        Call("Q", Call("shift", Num(1), V("x"))), Eq, Sp, Call("f", Call("Q", V("x")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactness gives a finite error window for a continuous true-orbit retraction, and exact shift equivariance turns it into global and two-sided limit shadowing for one fixed map.",
        H("Compact Pseudo-Orbit Selectors"), Blocks(
        Paragraph(Text("For a compact metric space M and homeomorphism f, e(x,i)=dist(x(i+1),f(x(i))) and "
            + "P_delta={x:Z->M : e(x,i)<=delta for every integer i}. Space is the entire closed subtype of the product topology. "
            + "The sequence space is not assigned a replacement metric. These conventions and the continuous true-orbit-fixing map are those of "
            + "Alfonso Artigue, Shadowing maps, arXiv:2504.00171v1, Sections 2.1 and 2.2. "
            + "The compactness argument below is a separate derivation; no novelty or resolution of the converse of Proposition 5.2 is asserted.")),
        Paragraph(Text("Each link error is continuous. The domain is the intersection of its closed sublevel sets, hence is closed and compact. "
            + "shift(k) is the homeomorphism x(i) to x(k+i), with inverse shift(-k), on that same domain. "
            + "orbit(f,p)(i)=(f^i)(p) uses integer powers of the homeomorphism, so negative times are included. "
            + "Its zero coordinate is p, its next coordinate is f of the current one, its shifts are true orbits of the corresponding iterates, "
            + "and it lies in P_delta whenever delta>=0. A full sequence with every error zero equals the true orbit of its zero coordinate.")),
        Paragraph(Text("In the displayed statements, Space(f,delta)=P_delta, trueOrbit(f,delta,p) is the true orbit included in that domain, "
            + "and inclusion(gamma,delta,x) is the continuous inclusion P_gamma to P_delta when gamma<=delta. "
            + "TendstoCofiniteZero(g) means Tendsto g cofinite (nhds 0). "
            + "The function e(x) sends i to e(x,i), and tracingError(f,Q,x) sends i to dist((f^i)(Q(x)),x(i)).")),
        Describe.Lean(DescribeId.Create("compact-selector-finite-window"), DeclarationHandle.Create(Owner + "finite_window"),
            H("A finite edge window derived from compactness"), StatementSource.FromAuthor(St([.. Selector(),
                Seq(AllEps, Exists, Sp, V("T"), InMacro, Sp, N, Comma, Sp,
                    Exists, Sp, V("eta"), InMacro, Sp, R, Comma, Sp, Num(0), Lt, Sp, V("eta"), Land, Sp, AllIn("x", P("delta"))),
                Hyp(Seq(AllIn("i", Z), Call("natAbs", V("i")), Le, Sp, V("T"), Rightarrow, Sp,
                    E(V("i")), Le, Sp, V("eta"))),
                Seq(Call("dist", Call("Q", V("x")), Call("x", Num(0))), Lt, Sp, V("eps"))])),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/artigue2025shadowing")), Blocks(
                Paragraph(Text("The tolerance eta and natural window radius T depend on eps and the fixed selector, not on the sequence. "
                    + "Assuming failure, choose x(n) with all errors in radius n at most 1/(n+1) and discrepancy at least eps. "
                    + "CompactSpace.tendsto_subseq applies to the closed subtype: a countable product of metric spaces is first countable. "
                    + "For each fixed integer edge, the increasing subsequence index eventually contains that edge in the tested window. "
                    + "Continuity of the link error and convergence of the reciprocal bounds force its limit to be zero. "
                    + "The limit is therefore a genuine bi-infinite orbit. Continuity of Q and its true-orbit identity force the limiting discrepancy to zero, contradicting eps>0. "
                    + "Compactness proves the window; no local-window or shadowing condition is assumed."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("compact-selector-all-centers"), DeclarationHandle.Create(Owner + "finite_window_all_times"),
            H("The same window at every integer center"), StatementSource.FromAuthor(St([.. Selector(), Equivariance,
                Seq(AllEps, Exists, Sp, V("T"), InMacro, Sp, N, Comma, Sp,
                    Exists, Sp, V("eta"), InMacro, Sp, R, Comma, Sp, Num(0), Lt, Sp, V("eta"), Land, Sp,
                    AllIn("x", P("delta")), AllIn("k", Z)),
                Hyp(Seq(AllIn("i", Z), Call("natAbs", V("i")), Le, Sp, V("T"), Rightarrow, Sp,
                    E(Seq(V("k"), Plus, V("i"))), Le, Sp, V("eta"))),
                Seq(D(V("k")), Lt, Sp, V("eps"))])),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Only the one-step identity Q(shift(1,x))=f(Q(x)) is assumed. "
                + "Integer induction, using invertibility for the negative step, proves Q(shift(k,x))=(f^k)(Q(x)) for every integer k. "
                + "Apply the compactness window to shift(k,x). Its edge i is the original edge k+i and its zero coordinate is x(k). "
                + "The input is still an arbitrary member of the same full P_delta, with no condition on errors outside the tested window."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("compact-selector-global-and-limit"), DeclarationHandle.Create(Owner + "global_and_limit_shadowing"),
            H("Global and limit tracing by one fixed selector"), StatementSource.FromAuthor(St([.. Selector(true), Equivariance,
                Seq(Open, AllEps, Exists, Sp, V("gamma"), InMacro, Sp, R, Comma, Sp,
                    Num(0), Lt, Sp, V("gamma"), Le, Sp, V("delta"), Land),
                Seq(AllIn("x", P("gamma")), AllIn("k", Z), RestrictedD(V("k")), Lt, Sp, V("eps"), Close, Land),
                Seq(Open, AllIn("x", P("delta")), Call("TendstoCofiniteZero", Call("e", V("x"))), Rightarrow),
                Seq(Open, AllEps, Exists, Sp, V("N"), InMacro, Sp, N, Comma, Sp, AllIn("k", Z),
                    V("N"), Le, Sp, Call("natAbs", V("k")), Rightarrow, Sp, D(V("k")), Lt, Sp, V("eps"), Close, Land),
                Seq(Call("TendstoCofiniteZero", Call("tracingError", V("f"), V("Q"), V("x"))), Close)])),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The Lean statement quantifies over Q once, before both conclusions. For global accuracy eps choose gamma=min(delta,eta)>0. "
                    + "Every sequence with all errors <=gamma satisfies the window at every integer center. "
                    + "The statement quantifies directly over every x in P_gamma and evaluates Q on the continuous inclusion into P_delta. "
                    + "Neither Q nor the original domain is reconstructed after choosing eps or x.")),
                Paragraph(Text("For the limit conclusion x is any member of the original P_delta. From cofinite convergence of its errors, choose A with e(x,i)<=eta whenever natAbs(i)>=A. "
                    + "For natAbs(k)>=A+T and natAbs(i)<=T, the integer triangle inequality gives natAbs(k+i)>=A. "
                    + "The all-center window therefore bounds the tracing error at k by eps. "
                    + "Finite exceptional sets of integers are equivalent to a sufficiently large natAbs threshold; this converts the explicit tail conclusion back to cofinite convergence. "
                    + "The same map thus satisfies the L-shadowing-map implication on every smaller global tolerance, while the two-sided limit conclusion holds on its entire original domain. "
                    + "Infinitely many, or all, errors may be nonzero.")),
                Paragraph(Text("This module assumes the existence of a continuous orbit retraction with exact shift equivariance. It does not construct the interval retraction R, the perturbed map T, "
                    + "or the every-rho witnesses against self-tuning. The original self-tuning distance remains the sum over all integer i of mu^natAbs(i) times dist(x(i),y(i)); "
                    + "no result about that weighted scalar or the full converse counterexample is supplied here."))), DescribeRole.Theorem)
        )));
}
