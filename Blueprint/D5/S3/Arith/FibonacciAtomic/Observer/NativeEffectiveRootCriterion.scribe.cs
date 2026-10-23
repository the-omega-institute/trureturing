using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeEffectiveRootCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete same-capacity coloring criterion and the particular acquired encoder and stationary reader.", H("Effective Native Birth Provenance Criterion"), Blocks(
            Paragraph(Text("Acquisition, authentication, actual complete export, lawful common entry, installation, and isolation remain the paid premises of Assumption 10.6. The program does not establish these physical or authority conditions.")),
            Paragraph(Text("Zero classes, zero calls, empty color cells, repeated occurrences, unused colors, and impossible branches remain in scope. The original feasibility predicate permits infinite ambient payload carriers with finite actual encoder range. The criterion preserves that original domain through the retained full feasibility equivalence.")),
            Paragraph(Text("The formulas suppress erased proof arguments to acquiredEncoder and coerce values and origins to their underlying data. Rho denotes substitution, and emptyList is the empty colored table.")),
            Entry("colorings", "Complete Finite Coloring Enumeration", "List.pi enumerates all functions from the executable attained chart to Fin r. Unused colors are allowed.", DescribeRole.Definition),
            Entry("colorPasses", "Exact Colored-Cell Test", "Only nonempty color cells impose a minimax budget test. The unit-call value is computed on the actual class-root menu, with q unchanged.", DescribeRole.Definition),
            Entry("decideNative", "Executable Finite Decision and Package", "The program searches the finite colorings and returns their color map with the actual minimax trees. Its data inputs are the finite row, r, and q; source and word bounds and actual origins are absent.", DescribeRole.Definition),
            Entry("effective_native_birth_provenance", "Full Corollary 10.9 and NBP.10.13", "For every finite cut set, prefix-free cut condition, complete row with nonempty actual image fiber, r at least one, and arbitrary natural q, a positive decision is equivalent to original InvFeas at the same r and q. Original InvFeas is also equivalent to a coloring whose every nonempty cell has minimax value at most q. NativeFullRootFeasibility.native_full_root_feasibility is applied directly.", DescribeRole.Theorem),
            Entry("acquiredEncoder", "Encoder from Actually Acquired Values", "The encoder applies the returned color map to the roots of the actually acquired class values. The row-validity and nonempty-origin premises are propositions erased by code generation; no actual origin is a runtime data argument.", DescribeRole.Definition),
            Entry("nativeEntry", "Representative-Address Installation", "NativeFullRootFeasibility.install compiles the selected finite tree to native calls at row-determined representatives. The unreachable fourth reply stops immediately. No equality or source-feasibility operation exists in this dialogue.", DescribeRole.Definition),
            Entry("returned_native_reader", "Correctness of the Particular Positive Output", "For the actual returned package, the acquired encoder has finite range of cardinality at most r. Its installed controller recovers the entire predecessor row in a stationary run with at most q answers on every actual filling and compatible origin. The proof uses the unchanged installation, run, and call-count suppliers and the full factorization theorem.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("nativeeffectiverootcriterion-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(Statement(n))) : StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Statement(string n)
    {
        var P=V("P"); var C=V("C"); var r=V("r"); var q=V("q"); var c=V("c"); var i=V("i");
        var pkg=V("pkg"); var v=V("v"); var u=V("u"); var tr=V("tr");
        var feasible=Call("InvFeas",P,C,r,q);
        var rows=Call("coloredRows",c,i);
        var coloring=Some("c",Fn(Call("Chart",C),Call("Fin",r)),
            All("i",Call("Fin",r),Imp(Seq(rows,Sp,Neq,Sp,V("emptyList")),
                LeOf(Call("minimaxValue",C,rows),q))));
        var criterion=And(IffOf(EqOf(Call("isSome",Call("decideNative",C,r,q)),V("true")),feasible),
            IffOf(feasible,coloring));
        var encoder=Call("acquiredEncoder",P,C,pkg);
        var run=Some("tr",V("Trace"),And(
            Call("Run",V("controller"),Call("nativeEntry",C,pkg,Call("acquiredEncoder",P,C,pkg,v)),
                D(0),Call("rho",u),tr,Call("canonicalRow",P,u)),
            Call("Stationary",tr),LeOf(Call("length",Call("answers",tr)),q)));
        var reader=And(Call("Finite",Call("range",encoder)),LeOf(Call("ncard",Call("range",encoder)),r),
            All("v",Call("ImageValues",C),All("u",Call("OriginFiber",P,C),
                Imp(EqOf(Call("rho",u),Call("evaluateRow",Call("extend",C,v),C)),run))));
        reader=All("pkg",Call("RootPackage",C,r),Imp(
            EqOf(Call("decideNative",C,r,q),Call("some",pkg)),reader));
        var result=n == "effective_native_birth_provenance" ? criterion : reader;
        result=All("r,q",V("Nat"),Imp(LeOf(D(1),r),result));
        result=All("C",V("LiteralRow"),Imp(Call("Nonempty",Call("OriginFiber",P,C)),result));
        return All("P",V("CutSet"),Imp(Call("CutPrefixFree",P),result));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. a]);
    private static Formula Fn(Formula a,Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula IffOf(Formula a,Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula And(params Formula[] a) => Seq(a.Select((x,i)=>i==0?Par(x):Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Names(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,Names(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Names(string n) => Seq(n.Split(',').Select((x,i)=>i==0?V(x):Seq(Comma,Sp,V(x))).ToArray());
}
