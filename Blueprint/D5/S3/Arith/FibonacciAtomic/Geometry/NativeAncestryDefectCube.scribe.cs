using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeAncestryDefectCubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent bracket choices in a native Fibonacci source preserve the leaf word and have an exact affine ancestor-area formula.",
        H("Native Ancestor Area Choices"), Blocks(
            Paragraph(Text("Sources are nonempty ordered binary trees with beta and alpha leaves. "
                + "The canonical source T at generation n is the n-fold Fibonacci substitution of alpha. "
                + "The left-associated source B and the right-associated source D both have leaf word beta, alpha, beta.")),
            Def("defectB", "The canonical three-leaf source", "B is pair(pair(beta,alpha),beta)."),
            Def("defectD", "The bracket defect", "D is pair(beta,pair(alpha,beta))."),
            Def("positions", "All literal three-leaf positions",
                "positions(t) consists of every actual address whose subtree in t is B."),
            Def("fill", "Simultaneous native choices",
                "fill(t,a) replaces B by D precisely at the original positions where the Boolean choice a is true."),
            Def("variant", "The finite-subset family",
                "variant(t,A) uses the membership indicator of A as the simultaneous choice."),
            Def("areaVector", "Euclidean ancestor-area vector",
                "areaVector(m,t) lists the products of the left and right child leaf counts in inorder gap order, "
                + "in Euclidean space with m minus one coordinates. Unoccupied coordinates are zero."),
            Def("gapVector", "One unit of transferred area",
                "gapVector(m,j) is the standard unit vector at j minus the standard unit vector at j plus one."),
            Describe.Lean(DescribeId.Create("native-area-cube"),
                DeclarationHandle.Create(Prefix + "native_area_cube"), H("The native family and its affine area formula"),
                StatementSource.FromAuthor(NativeFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n at least three, all B positions are counted by fib(n minus two). "
                        + "Distinct subsets give distinct actual trees. Every choice preserves the leaf word "
                        + "and the fib(n plus one) leaf count. The empty subset has intrinsic substitution "
                        + "depth n, and every nonempty subset has depth zero.")),
                    Paragraph(Text("Coordinates record the product of the two child leaf counts at each internal gap. "
                        + "Replacing B changes its two internal coordinates from [1,2] to [2,1]. "
                        + "An arbitrary context with equal-length fillings has the same exterior coordinate lists. "
                        + "Adding positions one at a time gives the stated sum of signed gap vectors."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));

    private static Formula NativeFormula()
    {
        Formula n = V("n"), a = V("A"), p = V("p");
        Formula t = Call("T", n), positions = Call("positions", t);
        Formula m = Call("fib", Seq(n, Plus, D(1)));
        Formula value = Call("variant", t, a);
        Formula word = EqOf(Call("wd", value), Call("wd", t));
        Formula length = EqOf(Call("length", value), m);
        Formula depth = EqOf(Call("depth", value),
            Call("ite", EqOf(a, Emptyset), n, D(0)));
        Formula transfer = Seq(new Formula.Subscript(Sum, Seq(p, Sp, InMacro, Sp, a)), Sp,
            Call("gapVector", m, Call("offset", t, p)));
        Formula affine = EqOf(Call("areaVector", m, value),
            Seq(Call("areaVector", m, t), Plus, transfer));
        Formula choices = All("A", Call("Finset", Op("Address")),
            Imp(Call("Subset", a, positions), And(word, And(length, And(depth, affine)))));
        Formula injective = Call("InjectiveOn", Call("variant", t), Call("powerset", positions));
        Formula count = EqOf(Call("card", positions), Call("fib", Seq(n, Minus, D(2))));
        return Disp(All("n", Nat(), Imp(Seq(D(3), Le, n), And(count, And(injective, choices)))));
    }
}
