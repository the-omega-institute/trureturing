using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class CombLiteralInstallationBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CombLiteralInstallationBounds", H("Literal installation and actual Read lower bounds"), Blocks(
            Paragraph(Text("A source is a nonempty full ordered Boolean tree. Source true is alpha and contributes zero to original parity; source false is beta and contributes one. Addresses use false for left and true for right. A controller has one common initial control and a source-free instruction function. Each Read row fixes its literal address and branches on exactly one of alpha, beta, branch or absent. A genuine Update substitutes the actual source and advances its epoch. Internal steps receive no source information; each Halt row has one fixed Boolean output.")),
            Paragraph(Text("Correct(M,h,T) requires sourcewise termination and original-parity correctness for every h-leaf source and every entry t at most T. Source shape, labels and entry are not control inputs. Run(M,u,e,t,qs,updates,f,b) records a first-halt execution from control e at epoch t; qs records actual Read occurrences with their epochs, and updates counts genuine Updates. These records are proof annotations, not additional mutable storage. Static(M,h,T) says every promised successful run has zero actual Updates; unreachable Update rows are allowed.")),
            Paragraph(Text("Queries and halts filter the entire finite control type, including unreachable installed rows. All mutable control is counted. The bounds allow unrestricted changes of control, so they apply in particular when each immediate change is restricted to hold or one bit. The proof is symbolic for arbitrary finite sizes, not a finite enumeration or a certified individual controller.")),
            Entry("successful_run_read_lower_bound", "Every successful run reads every original leaf", ReadStatement(),
                "For each original leaf, flipping just that leaf preserves the original length and changes parity. Until a separating Read the same controller follows the same run on the two sources, including genuine Updates. Such a Read must lie inside that original leaf cone. Distinct original leaf cones are disjoint, giving an injection from original leaves into Read occurrences on this particular run. No finite-control assumption is needed."),
            Entry("comb_installed_lower_bounds", "Complete installed union over all comb shapes", InstalledStatement(false),
                "For every address of length h minus one, the comb with that tip has exactly h leaves, including the empty tip at h=1. Opposite tip labels force an installed Read in that tip cone. Equal-depth tip cones are disjoint, giving the exponential query count across the entire family of shapes. Both parity outputs occur, requiring two distinct Halt rows disjoint from queries. The admissible no-11 word count is fib(width+2), so any injective encoding of the entire control type has the displayed Fibonacci capacity. This installed-union bound does not assert exponentially many Reads on one run."),
            Entry("static_comb_installed_lower_bounds", "Static installed union over all entries", InstalledStatement(true),
                "For each tip, a static controller must distinguish the adjacent atomic sources at every entry from zero through T. A separating suffix lies in a three-entry interval determined by its weighted depth, with left cost one and right cost two. An injection from entries to installed query rows paired with three slots yields the factor (T+3)/3, equal to the ceiling of (T+1)/3. Summing over disjoint tip cones gives the product bound. Natural division is used. The Fibonacci inequalities hold for every actual correct installation, hence also for a minimizing installation when one exists; neither existence nor attainment of a minimum is asserted here. In particular the conclusions include the positive regimes T=0 or even h without adding that restriction to these necessary bounds.")
        )));

    private static DocumentBlock Entry(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("comb-literal-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula ReadStatement() => All("E", V("Type"),
        All("M", Call("Controller", V("E")), All("h,T", V("Nat"),
        Imp(Call("Correct", V("M"), V("h"), V("T")),
        All("u", V("Source"), Imp(EqOf(Call("length", V("u")), V("h")),
        All("t", V("Nat"), Imp(Le(V("t"), V("T")),
        All("qs", Call("List", Prod(V("E"), V("Nat"))), All("updates", V("Nat"),
        All("f", V("E"), All("b", V("Bool"),
        Imp(Call("Run", V("M"), V("u"), Call("initial", V("M")), V("t"),
            V("qs"), V("updates"), V("f"), V("b")), Le(V("h"), Call("length", V("qs"))))))))))))))));

    private static Formula InstalledStatement(bool isStatic)
    {
        var n = Pow(D(2), Sub(V("h"), D(1)));
        if (isStatic) n = Mul(n, Call("div", Add(V("T"), D(3)), D(3)));
        var words = Seq(OpenBrace, V("w"), Colon, Sp,
            Arr(Call("Fin", V("width")), V("Bool")), Sp, Mid, Sp,
            Call("Adm", V("width"), V("w")), CloseBrace);
        var result = And(Le(n, Call("card", Call("queries", V("M")))),
            Le(D(2), Call("card", Call("halts", V("M")))),
            Le(Add(n, D(2)), Call("card", V("E"))),
            All("width", V("Nat"), All("encode", Arr(V("E"), words),
                Imp(Call("Injective", V("encode")), Le(Add(n, D(2)), Call("fib", Add(V("width"), D(2))))))));
        if (isStatic) result = Imp(Call("Static", V("M"), V("h"), V("T")), result);
        return All("E", V("Type"), Seq(OpenBracket, Call("Fintype", V("E")), CloseBracket, Sp,
            All("M", Call("Controller", V("E")), All("h,T", V("Nat"),
                Imp(Lt(D(0), V("h")), Imp(Call("Correct", V("M"), V("h"), V("T")), result))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Prod(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
}
