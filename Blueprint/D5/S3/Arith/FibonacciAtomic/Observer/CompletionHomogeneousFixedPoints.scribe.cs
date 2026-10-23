using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class CompletionHomogeneousFixedPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CompletionHomogeneousFixedPoints", H("Exhaustive completed homogeneous fixed-point split"), Blocks(
            Describe.Lean(DescribeId.Create("completion-homogeneous-fixed-point-split"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints.completed_homogeneous_split"),
                H("A homogeneous feedback equation has exactly the leafless solution or the atomic orbit"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("CompletionTree is the unrestricted PFunctor.M for Boolean leaves and ordered binary nodes. The native substitution rho changes true leaves to false leaves, expands false leaves to a pair, and distributes through every node. The theorem quantifies over every natural exponent a, every finite homogeneous FreeMagma Nat expression H with an explicit pair root, and every completed tree X. No finiteness, regularity, computability, or ground term is assumed for X.")),
                    Paragraph(Text("The finite branch uses the existing native mass and atomic-rank infrastructure. A positive-mass finite source cannot satisfy a pair-root feedback equation because the pair strictly increases mass; mass zero is exactly an atomic iterate. The existing completed injectivity of rho cancels the common atomic iterate, leaving precisely the test eval H (leaf true) = atomic a. Thus, when the test holds, every atomic iterate is a solution, and when it fails none is.")),
                    Paragraph(Text("For an infinite solution with a leaf, a frontier occurrence below a is transported back to an actually reached original subtree. The new infinite_feedback_descent relation recovers an infinite original Y, records the exact shifted iterate X = rho^(a-b) Y, and proves that Y satisfies the same feedback equation. Repeating this descent yields arbitrarily large shifts while the leaf remains present; the existing full-prefix argument then forces an impossible unbounded finite leaf depth. The remaining infinite solution is therefore the unique leafless tree Omega.")),
                    Paragraph(Text("The reverse directions are constructive: Omega is fixed by every iterate and every homogeneous pair expression, while each atomic iterate satisfies the equation whenever the alpha test holds by iterate commutation and homogeneity. PairRoot records the one-residual syntax boundary, excluding a lone residual, ground terms, and a second independent residual. The result formalizes the complete Theorem 2.3 split and its finite-solution consequence inside the unrestricted completed domain; it claims no external literature novelty."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var left = EqOf(Call("rhoIterate", V("a"), V("X")), Call("eval", V("H"), V("X")));
        var atomic = AndOf(EqOf(Call("eval", V("H"), Call("leafTrue")), Call("atomic", V("a"))),
            Some("c", V("Nat"), EqOf(V("X"), Call("atomic", V("c")))));
        return StatementSource.FromAuthor(Disp(All("a", V("Nat"), All("H", Call("Homogeneous"),
            All("root", Call("PairRoot", V("H")), All("X", Call("CompletionTree"),
                IffOf(left, OrOf(EqOf(V("X"), Call("Omega")), atomic))))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula OrOf(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
