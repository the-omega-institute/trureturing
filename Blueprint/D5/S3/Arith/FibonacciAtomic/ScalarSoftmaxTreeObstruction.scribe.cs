using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ScalarSoftmaxTreeObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ScalarSoftmaxTreeObstruction.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, Par(Seq(x, Colon, Sp, type)), Comma, Sp, body));
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar bilinear trees with three affine logits have uniform classification, square and log risk floors.",
        H("Scalar Softmax Trees and a Three-Class Obstruction"),
        Blocks(
            Paragraph(Text("Let m be any natural number and n=m+3. Word(m) is the full function "
                + "space Fin(n) to Window, with positions starting at zero. Window has exactly the "
                + "five low-to-high bit strings 000,100,010,101,001. The uniform law averages over "
                + "all raw words, without restricting seams or terminal windows. Each word has "
                + "mass 5 to the power minus n; independence concerns complete windows.")),
            Paragraph(Text("The existing first-rejection diagnostic task uses zero-based seam "
                + "labels and a final terminal label. coarse(w) is 1 when task(w) is its label 0, "
                + "2 when task(w) is its label 1, and 0 for every other diagnostic or acceptance. "
                + "Consequently it is 1 when last(w(0)) and first(w(1)) are true, otherwise 2 "
                + "when last(w(1)) and first(w(2)) are true, and otherwise 0. All-zero windows "
                + "still occupy coordinates. Here last is the high bit and first the low bit.")),
            Paragraph(Text("A task tree is full, its leaf labels are distinct, and its leaf set "
                + "is all Fin(n). Each encoder f(i) is an arbitrary real function on Window. "
                + "B(l,r) is an arbitrary real bilinear map from two real lines to the real line. "
                + "scalarImplementation uses the existing tree evaluator with these encoders and "
                + "mergers. Its value on an unused empty storage tree is zero. Every task message "
                + "is scalar; a zero-dimensional message embeds as the constant zero coordinate. "
                + "There are no additional inputs, input-dependent controls or internal affine constants. "
                + "A bilinear map on real scalars is B(1,1) times the product of its arguments. "
                + "Induction on the tree gives a coefficient times the product of its leaf values.")),
            Paragraph(Text("The head parameters u and v are arbitrary functions Fin(3) to the "
                + "reals. logit(u,v,z,y)=u(y)z+v(y); probability is its exponential divided by "
                + "the sum of all three exponentials. maxima is the set of maximal logit labels. "
                + "LegalChoice(choose) means that choose selects a member of every nonempty "
                + "label set. prediction uses this fixed function of maxima alone. errorRisk "
                + "averages its error indicator; squareRisk averages the sum over all three "
                + "labels of squared errors against the one-hot coarse label, without division "
                + "by three; logRisk averages minus the natural logarithm of the true-class probability.")),
            Describe.Lean(DescribeId.Create("scalar-softmax-tree-obstruction"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Three Uniform Risk Floors"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All tree shapes, leaf functions, bilinear mergers and "
                    + "affine head parameters are quantified. The classification bound holds for "
                    + "every legal fixed choice rule. The two proper-loss bounds do not depend on "
                    + "a choice rule. The constants are uniform lower certificates, without an "
                    + "assertion of optimality or attainability.")),
                    Paragraph(Text("Fix any tail. On first-window choices 000 and 001, "
                        + "middle-window choices 100 and 001, and third-window choices 000 and "
                        + "100, the two middle slices have classes by rows 0,1 and by columns "
                        + "0,2. Changing the middle window scales all four scores by a common "
                        + "factor. Each deterministic three-logit decision set is an interval, "
                        + "possibly a singleton or empty, including coincident logits and all "
                        + "ties. Two different interval classes separate their two pairs strictly. "
                        + "The row and column separations contradict each other, so some actual "
                        + "word is misclassified on every tail. Its conditional mass is 1/125. "
                        + "On an error a competing class has probability at least that of the "
                        + "true class; the latter is at most one half. The full square loss is "
                        + "at least one half and the log loss at least log(2). Averaging over "
                        + "every tail gives the three bounds."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var m = V("m");
        var n = Seq(m, Plus, D(3));
        var t = V("t");
        var f = V("f");
        var b = V("B");
        var u = V("u");
        var v = V("v");
        var c = V("choose");
        var r = Call("Real");
        var labels = Call("Fin", D(3));
        var tree = Call("Tree", Call("Fin", n));
        var z = Call("evaluate", Call("scalarImplementation", f, b), t);
        var error = All(c, Seq(Call("Finset", labels), Sp, To, Sp, labels),
            Seq(Call("LegalChoice", c), Sp, Implies, Sp,
                new Formula.Fraction(D(1), D(125)), Sp, Le, Sp,
                Call("errorRisk", z, u, v, c)));
        var square = Seq(new Formula.Fraction(D(1), D(250)), Sp, Le, Sp,
            Call("squareRisk", z, u, v));
        var log = Seq(new Formula.Fraction(Call("log", D(2)), D(125)), Sp, Le, Sp,
            Call("logRisk", z, u, v));
        var condition = And(Call("Full", t),
            Seq(Call("leaves", t), Sp, Eq, Sp, Call("univ")));
        var body = Seq(condition, Sp, Implies, Sp, And(error, And(square, log)));
        return Disp(All(m, Call("Nat"), All(t, tree,
            All(f, Seq(Call("Fin", n), Sp, To, Sp, Call("Window"), Sp, To, Sp, r),
            All(b, Seq(tree, Sp, To, Sp, tree, Sp, To, Sp, Call("Bilinear", r, r, r)),
            All(u, Seq(labels, Sp, To, Sp, r), All(v, Seq(labels, Sp, To, Sp, r), body)))))));
    }
}
