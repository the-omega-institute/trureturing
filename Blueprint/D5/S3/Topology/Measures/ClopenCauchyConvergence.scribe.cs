using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class ClopenCauchyConvergenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/ClopenCauchyConvergence.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Fn(Formula source, Formula target) => Seq(source, Sp, To, Sp, target);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Signed(Formula K) => Call("SignedMeasure", K);
    private static Formula TV(Formula s) => Call("totalVariationRealUniv", s);
    private static Formula At(Formula f, string n) => Call("apply", f, V(n));
    private static Formula Weak(Formula s) =>
        Call("toWeakDual", Call("signedFunctional", s));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Seq(V("Type"), Underscore, Grp(V("u")))),
            Inst("MetricSpace", V("K")), Inst("CompactSpace", V("K")),
            Inst("TotallyDisconnectedSpace", V("K")),
            Inst("MeasurableSpace", V("K")), Inst("BorelSpace", V("K"))),
        Seq(All("C", Call("Real")), All("s", Fn(Call("Nat"), Signed(V("K"))))),
        Seq(Call("Nonneg", V("C")), Sp, Rightarrow, Sp,
            Grp(Seq(All("n", Call("Nat")), TV(At(V("s"), "n")), Sp, Le, Sp, V("C"))), Sp,
            Rightarrow, Sp,
            Grp(Seq(All("A", Call("Set", V("K"))), Call("IsClopen", V("A")), Sp,
                Rightarrow, Sp, Call("CauchySeq", Seq(V("n"), Sp, Mapsto, Sp,
                    Call("apply", At(V("s"), "n"), V("A"))))))), Sp,
        Seq(Rightarrow, Sp, Exists, Sp, V("mu"), Colon, Signed(V("K")), Comma, Sp,
            TV(V("mu")), Sp, Le, Sp, V("C"), Sp, Land, Sp,
            Call("Regular", Call("jordanPosPart", V("mu"))), Sp, Land, Sp,
            Call("Regular", Call("jordanNegPart", V("mu"))), Sp, Land, Sp,
            Call("Tendsto", Seq(V("n"), Sp, Mapsto, Sp, Weak(At(V("s"), "n"))),
                Call("atTop"), Call("nhds", Weak(V("mu")))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clopen Cauchy values determine a represented signed weak-star whole-sequence limit under a uniform total-variation bound.",
        H("Full signed weak-star convergence from clopen Cauchy data"),
        Blocks(
            Paragraph(Text(
                "K is an arbitrary compact metric, totally disconnected Borel space, including the empty space. "
                + "For a real C with 0 ≤ C and an arbitrary sequence of actual finite signed measures s, "
                + "assume only the uniform total-variation bound and Cauchy convergence of s(n)(A) for every clopen A.")),
            Describe.Lean(
                DescribeId.Create("signed-functional-clopen-evaluation"),
                DeclarationHandle.Create(Owner + "signedFunctional_charFn"),
                H("Exact signed clopen evaluation"),
                StatementSource.FromAuthor(Disp(Seq(
                    All("K", Seq(V("Type"), Underscore, Grp(V("u")))),
                    Inst("MetricSpace", V("K")), Inst("CompactSpace", V("K")),
                    Inst("TotallyDisconnectedSpace", V("K")),
                    Inst("MeasurableSpace", V("K")), Inst("BorelSpace", V("K")),
                    All("r", Signed(V("K"))), All("A", Call("Set", V("K"))),
                    Call("IsClopen", V("A")), Sp, Rightarrow, Sp,
                    Call("signedFunctional", V("r"), Call("charFnContinuousMap", V("A"))),
                    Sp, Eq, Sp, Call("apply", V("r"), V("A"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real characteristic function of a clopen A integrates exactly to r(A). "
                    + "This consumed evaluation identity connects old weak-star F to exact clopen values in SignedProperLimit. "
                    + "The proof and statement are the existing signed integral identity; no new measure representation is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tendsto-signed-functional-of-clopen-cauchy"),
                DeclarationHandle.Create(Owner + "tendsto_signedFunctional_of_clopen_cauchy"),
                H("Represented signed whole-sequence convergence criterion"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The conclusion supplies an actual SignedMeasure μ with the same real total-variation bound, regular positive and negative Jordan parts, and weak-star convergence of the represented signed functionals. "
                        + "There is no positivity assumption, no pre-assumed full convergence, no finite-support restriction, and no strict positivity or nonemptiness premise.")),
                    Paragraph(Text(
                        "The proof first uses the existing compact metric signed subsequence theorem. "
                        + "On a clopen A, the characteristic locally constant function evaluates the signed functional exactly at s(n)(A). "
                        + "The scalar Cauchy hypothesis and the strictly monotone convergent subsequence therefore force the whole scalar sequence to converge to μ(A).")),
                    Paragraph(Text(
                        "Every real locally constant function on compact K has finite range and clopen fibres. "
                        + "The existing vector-measure simple-function formula turns its integral into a finite sum of those clopen values, so locally constant tests converge. "
                        + "The existing locally constant Stone–Weierstrass closure theorem, NormedSpace.equicontinuous_TFAE, and EquicontinuousAt.tendsto_of_mem_closure extend convergence to every continuous test. The operator bound is consumed directly from NormPreservingLifts.signedFunctional_norm_le; the weak-dual evaluation criterion finishes the result. This criterion is a live helper in SignedSplitReferenceConvergence, rather than a separate new-content claim.")),
                    Paragraph(Text(
                        "Regularity is inherited from the compact metric Borel finite-measure instances for the two Jordan parts. "
                        + "This is the analytic composition needed by the same successor/proper-limit construction. It does not construct the transfinite system, settle CH bookkeeping, or solve Talagrand Problem 8.2."))),
                DescribeRole.Theorem))));
}
