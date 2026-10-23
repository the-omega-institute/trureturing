using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiniteRootMinimaxDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executable attained chart and exact unit-call optimum on the actual three-reply menu.", H("Finite Actual Root Menu Minimax"), Blocks(
            Paragraph(Text("The actual menu consists only of the classes occurring in the complete current row. The three replies are some true, some false, and none. The fourth native absent reply has no table row.")),
            Paragraph(Text("This natural-number executable optimizer supplies the effective part of Native Birth Provenance Corollary 10.9. It adds no physical-cost or performance claim. Finite normalization and Bellman methods are existing suppliers; the particular row-count-fueled construction and its attaining-tree theorem are the mathematical content here.")),
            Paragraph(Text("In the formula, rowType and rowTarget denote the TableRow projections; chart elements coerce to their assignments. The two Boolean implications express the exact constant versus nonconstant recurrence.")),
            Entry("admissibleCode", "Attained Type Checker", "The Boolean image grammar and distinct-class leaf bounds decide precisely Admissible. The branch obligation remains in the retained native image-chart supplier.", DescribeRole.Definition),
            Entry("admissibleCode_spec", "Exact Boolean Admissibility", "The public equivalence connects the executable checker to the original admissibility predicate for every literal row and every class-root assignment. It is reused by the actual repeated-partner controllers.", DescribeRole.Theorem),
            Entry("chartList", "Finite Chart Enumeration", "List.pi enumerates the three replies at every appearing class and filters by admissibleCode. Completeness includes zero classes. No actual origin, source-size bound, or native-word bound is a data argument.", DescribeRole.Definition),
            Entry("computedTarget", "Entire Predecessor Target", "The computable mask tests each occurrence parent for the visible alpha sibling and calls NativePredecessorRowRecovery.back. Shared old and new occurrences are repaired individually, including the root and blocked cuts.", DescribeRole.Definition),
            Entry("minimaxValue", "Executable Unit-Call Value", "Row-count fuel suffices: every nonempty reply fiber of a splitting coordinate is strictly smaller. A constant target costs zero. Otherwise List.argmin selects the actual class coordinate with one plus the maximum child value. Empty reply cells contribute zero.", DescribeRole.Definition),
            Entry("minimaxTree", "Particular Attaining Tree", "The tree follows the same argmin and three reply cells as minimaxValue. Constant tables stop at their common complete target. Empty and impossible branches stop at the supplied fallback.", DescribeRole.Definition),
            Entry("finite_root_minimax", "Exact Recurrence and Finite Chart Bound", "The retained result combines the constant-target or splitting-menu recurrence, attaining tree, all-competitor lower bound, chart length at most 3 raised to the number of occurring classes, exact semantic chart completeness, and computed-target agreement.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("nativefiniterootminimax-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(Statement(n))) : StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Statement(string n)
    {
        var C=V("C"); var W=V("W"); var a=V("a"); var T=V("T"); var theta=V("theta");
        if (n == "admissibleCode_spec") return All("C",V("LiteralRow"),
            All("theta",Fn(Call("Classes",C),Call("Option",V("Bool"))),
                Seq(Par(EqOf(Call("admissibleCode",C,theta),V("true"))),Sp,Iff,Sp,
                    Par(Call("Admissible",C,theta)))));
        var value=Call("minimaxValue",C,W);
        Formula Correct(Formula tree) => All("a",Call("TableRow",C),Imp(
            Call("member",a,W),EqOf(Call("fst",Call("rootRun",Call("rowType",a),tree)),Call("rowTarget",a))));
        var recurrence=And(
            Imp(EqOf(Call("constantTarget",W),V("true")),EqOf(value,D(0))),
            Imp(EqOf(Call("constantTarget",W),V("false")),EqOf(value,
                Call("scoreMinimum",C,W,Call("minimaxValue",C)))));
        var tree=Call("minimaxTree",C,V("fallback"),W);
        var result=And(recurrence,
            All("fallback",V("LiteralRow"),And(Correct(tree),EqOf(Call("rootDepth",tree),value))),
            All("T",Call("RootTree",C,V("LiteralRow")),Imp(Correct(T),LeOf(value,Call("rootDepth",T)))),
            LeOf(Call("length",Call("chartList",C)),Call("pow",D(3),Call("card",Call("Classes",C)))),
            All("theta",Call("Chart",C),Call("member",theta,Call("chartList",C))),
            All("theta",Fn(Call("Classes",C),Call("Option",V("Bool"))),
                EqOf(Call("computedTarget",C,theta),Call("target",C,theta))));
        return All("C",V("LiteralRow"),All("W",Call("List",Call("TableRow",C)),result));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula Fn(Formula a,Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula And(params Formula[] a) => Seq(a.Select((x,i)=>i==0?Par(x):Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Names(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Names(string n) => Seq(n.Split(',').Select((x,i)=>i==0?V(x):Seq(Comma,Sp,V(x))).ToArray());
}
