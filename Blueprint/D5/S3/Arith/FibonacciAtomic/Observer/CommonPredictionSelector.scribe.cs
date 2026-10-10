using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class CommonPredictionSelectorDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, F.Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One deterministic majority selector balances all teachers in every rare-symbol class.", H("A Common Balanced Priority Selector"), Blocks(
            Paragraph(Text("The teacher family consists of a left and a right teacher for every prefix position. label(false,i,x) is the left teacher and label(true,i,x) is the right teacher. errorCount(z,side,i,f) counts classification mistakes on all words in rare-symbol class z.")),
            Paragraph(Text("A permutation of prefix coordinates preserves the reservoir, rare count and exterior majority selector. Swapping i and j transports the teacher label at i to the label at j, so the exterior error count is constant within each layer.")),
            Paragraph(Text("In each reservoir class choose one subset whose size cancels the exterior discrepancy. The same chosen subset receives label two; its complement receives label zero. Outside the reservoir the classifier uses the exterior majority selector. This single function attains a majority label at every input.")),
            Paragraph(Text("Each left teacher receives exactly the chosen subset size as its reservoir errors. Each right teacher receives the complement size. Their errors are equal because of the split equation, and prefix symmetry equalizes all coordinates within a layer. The construction balances every class z simultaneously.")),
            Paragraph(Text("The selection uses finite subset existence and classical choice. It establishes a deterministic function of the complete input word. It does not specify a computable or lexicographic implementation.")),
            Describe.Lean(DescribeId.Create("common-selector"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSelector.uniform_mass_balanced"),
                H("Simultaneous classwise balance and pointwise majority"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the reservoir subsets once for all mass classes. The same classifier is used for every teacher and every class. The exterior discrepancy identity and integer split equation equate the two layers, while the prefix permutation equates coordinates within a layer."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var majority = All("x", Call("Input", Seq(V("m"), Plus, D(3))),
            All("c", Call("Fin", D(3)),
                Le(Call("actualVotes", V("x"), V("c")),
                   Call("actualVotes", V("x"), Call("f", V("x"))))));
        var balanced = All("z", V("Nat"), All("i", Call("Fin", V("m")),
            All("j", Call("Fin", V("m")),
                And(Eq(Call("errorCount", V("z"), V("false"), V("i"), V("f")),
                       Call("errorCount", V("z"), V("false"), V("j"), V("f"))),
                    Eq(Call("errorCount", V("z"), V("false"), V("i"), V("f")),
                       Call("errorCount", V("z"), V("true"), V("j"), V("f")))))));
        return All("m", V("Nat"), Imp(Seq(D(0), Sp, Lt, Sp, V("m")),
            Ex("f", Call("Classifier", V("m")), And(majority, balanced))));
    }
}
