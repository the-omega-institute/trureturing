using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeCompletionSupportClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeCompletionSupportClosure", H("Signed native support and exact product closure"), Blocks(
            Describe.Lean(DescribeId.Create("native-completion-support-closure"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionSupportClosure.support_closure_iff"),
                H("Every finite neighborhood is feasible exactly when the scalar support accumulates"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There are k scalar coordinates and m native residual names. P is any predicate on the scalar tuple, including a Presburger predicate. Each member of pairs is a pair of existing RankedExpr expressions; Negatives pairs n z requires every listed disequality to hold for the same actual finite residual tuple z at the same scalar tuple n. Repeated residual names retain one common value. Scalar syntax, ground trees and native substitutions have their existing interpretations.")),
                    Paragraph(Text("An Option Nat value represents a scalar completion: some a is the isolated finite point a, and none is the divergent point. ScalarNear limit bound n fixes n(i) to a at every finite coordinate and requires bound(i) at most n(i) at every divergent coordinate. The complete bound vector is satisfied simultaneously by one n. Separate unboundedness of coordinate projections is not the condition.")),
                    Paragraph(Text("Support P pairs T n means P(n) and the existence of one finite z satisfying every negative, with z(i) equal to t whenever embed(t) equals T(i). Thus every actually finite coordinate of T is fixed, and every nonfinite coordinate remains free. Embedding injectivity follows by applying the existing finite-source leaf readout uniqueness theorem. The support is the full feasible support, not the image of a selected representative family.")),
                    Paragraph(Text("JointClosure quantifies over every scalar bound vector and every residual height vector. For each pair of vectors it requires one n and one finite z satisfying ScalarNear, P, all negatives, and every four-valued address reply through each requested height. This is the finite scalar and prefix neighborhood definition of closure. It neither evaluates a signed predicate on the limit trees nor asserts that one finite tuple matches an infinite tree at all depths.")),
                    Paragraph(Text("For the forward direction, a finite coordinate is isolated by a height bounding all leaf addresses of its finite source. Existing source_foundation then forces equality of any finite source with that reply table. Taking those heights for all coordinates in the joint neighborhood gives a support point at every scalar bound, retaining that single scalar tuple throughout.")),
                    Paragraph(Text("For the reverse direction, choose one support point n and its full negative-conjunction seed. Partition all original residual indices by exact membership in the finite embedding. Fintype.equivFin and Equiv.sumCompl identify this partition with a fixed block and a free block; expression substitution reindexes names without splitting repeated occurrences. The nonfinite completion theorem supplies an actual infinite branch on every free coordinate. Apply simultaneous_prefix_disequality once to the whole transformed list, the unchanged n and all independently requested heights. Reassemble the original coordinates, using exact finite embedding equalities on the fixed block.")),
                    Paragraph(Text("Both dimensions may be zero, the negative list may be empty, and names may be unused. Finite coordinates impose equalities and divergent coordinates impose joint lower bounds even in these cases. The result is an existence theorem for normalized Cartesian native pieces. It does not supply a decision of the unknown finite coordinate set, a Presburger witness-extraction implementation, arbitrary positive residual constraints, the general NIC criterion, acquisition costs or resource bounds. The closure argument is a native application of existing finite separation and the classical branch correspondence; no literature originality is claimed."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var scalars = Arr(Call("Fin", V("k")), V("Nat"));
        var expr = Call("RankedExpr", V("k"), V("m"));
        var result = IffOf(Call("JointClosure", V("P"), V("pairs"), V("limit"), V("T")),
            All("bound", scalars, Some("n", scalars,
                AndOf(Call("ScalarNear", V("limit"), V("bound"), V("n")),
                    Call("Support", V("P"), V("pairs"), V("T"), V("n"))))));
        return StatementSource.FromAuthor(Disp(All("k,m", V("Nat"),
            All("P", Arr(Par(scalars), V("Prop")),
                All("pairs", Call("List", Call("Prod", expr, expr)),
                    All("limit", Arr(Call("Fin", V("k")), Call("Option", V("Nat"))),
                        All("T", Arr(Call("Fin", V("m")), V("CompletionTree")), result)))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
