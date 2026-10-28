using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.PostLie;
internal sealed class AriWordProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/PostLie/AriWordProduct";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/burmesterkuhn2025postlie");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Ordered primitive unshuffle and rational ari product", H("AriWordProduct"), Blocks(
        Paragraph(Text("N includes zero. H is the rational concatenation-word algebra and Word its ordinary basis index type. Functions to Fin(n) assign each original position to one slot. Tuple words multiply componentwise by concatenation. Every assignment is summed separately; identical resulting tuples are not deduplicated. List products retain their displayed order.")),
        Entry("slot", "slot", "slot", Q("n",V("N"),Q("a",V("N"),Q("A",Call("List",V("N")),Q("f",Arrow(Call("Fin",Add(Call("length",V("A")),Num(1))),Call("Fin",V("n"))),Q("j",Call("Fin",V("n")),And(Equal(Call("slot",V("empty"),V("f"),V("j")),Num(1)),Equal(Call("slot",Call("cons",V("a"),V("A")),V("f"),V("j")),Call("ifThenElse",Equal(App(V("f"),Num(0)),V("j")),Multiply(Call("of",V("a")),Call("slot",V("A"),Call("tail",V("f")),V("j"))),Call("slot",V("A"),Call("tail",V("f")),V("j")))))))))), "For f:Fin(length(A))->Fin(n), the slot j is the subsequence of A whose positions map to j. The recursive tail of f is i mapped to f(succ(i)).", DescribeRole.Definition),
        Entry("primitiveUnshuffle", "primitiveUnshuffle", "primitiveUnshuffle", Q("n",V("N"),Equal(Call("primitiveUnshuffle",V("n")),Call("FreeMonoidLift",Call("lambda",V("a"),Sum(Call("Fin",V("n")),"j",Call("single",Call("update",Call("constant",Num(1)),V("j"),Call("of",V("a"))),Num(1))))))), "This monoid homomorphism is the free-monoid lift of the primitive sum. Its target is MonoidAlgebra Q of the n-tuples of original words; the tuple with a single nonempty slot represents placement in that tensor factor.", DescribeRole.Definition),
        Entry("primitiveUnshuffle-assignments", "primitiveUnshuffle_assignments", "primitiveUnshuffle_assignments", Q("n",V("N"),Q("A",Call("List",V("N")),Equal(Call("primitiveUnshuffle",V("n"),Call("ofList",V("A"))),Sum(Arrow(Call("Fin",Call("length",V("A"))),Call("Fin",V("n"))),"f",Call("single",Call("lambda",V("j"),Call("slot",V("A"),V("f"),V("j"))),Num(1))))))), "This proves the equality of the primitive multiplicative expansion with all ordered position assignments, including empty words and zero slots.", DescribeRole.Theorem),
        Entry("orderedTerm", "orderedTerm", "orderedTerm", Q("B",V("Word"),Q("S",Arrow(Call("Fin",Add(Call("length",V("B")),Num(1))),V("Word")),Equal(Call("orderedTerm",V("B"),V("S")),Multiply(WB(App(V("S"),Num(0))),Call("listProd",Call("ofFn",Call("lambda",V("j"),LA(App(V("S"),Call("succ",V("j"))),Call("get",V("B"),V("j")))))))))), "S has domain Fin(length(B)+1). Slot zero is concatenated with the list product of the actions of each successor slot on the corresponding original letter of B.", DescribeRole.Definition),
        Entry("starWord", "starWord", "starWord", Q("A",V("Word"),Q("B",V("Word"),Equal(Call("starWord",V("A"),V("B")),Sum(Arrow(Call("Fin",Call("length",V("A"))),Call("Fin",Add(Call("length",V("B")),Num(1)))),"f",Call("orderedTerm",V("B"),Call("lambda",V("j"),Call("slot",Call("toList",V("A")),V("f"),V("j")))))))), "The summation domain is every position assignment, not the set of distinct slot tuples.", DescribeRole.Definition),
        Entry("starWord-unshuffle", "starWord_unshuffle", "starWord_unshuffle", Q("A",V("Word"),Q("B",V("Word"),Equal(Call("starWord",V("A"),V("B")),Call("apply",Call("basisConstrQ",Call("MonoidAlgebraBasis",Arrow(Call("Fin",Add(Call("length",V("B")),Num(1))),V("Word"))),Call("orderedTerm",V("B"))),Call("primitiveUnshuffle",Add(Call("length",V("B")),Num(1)),V("A")))))), "The linear extension of orderedTerm is applied to the actual primitive unshuffle. This is the finite source product presentation of Proposition 2.1.", DescribeRole.Theorem),
        Entry("star", "star", "star", Q("P",V("H"),Q("Q",V("H"),Equal(Call("star",V("P"),V("Q")),Sum(Call("support",V("P")),"A",Sum(Call("support",V("Q")),"B",Multiply(Multiply(Coeff(V("P"),V("A")),Coeff(V("Q"),V("B"))),Call("starWord",V("A"),V("B")))))))), "This is the rational bilinear extension of the ordered primitive-unshuffle construction. The displayed finite-support formula follows from its basis values.", DescribeRole.Definition),
        Entry("star-basis", "star_basis", "star_basis", Q("A",V("Word"),Q("B",V("Word"),Equal(Call("star",WB(V("A")),WB(V("B"))),Call("starWord",V("A"),V("B"))))), "The bilinear primitive construction has exactly the assignment-defined basis values.", DescribeRole.Theorem),
        Entry("starWord-homogeneous", "starWord_homogeneous", "starWord_homogeneous", Q("A",V("Word"),Q("B",V("Word"),Mem(Call("starWord",V("A"),V("B")),Call("homogeneous",Add(Call("weight",V("A")),Call("weight",V("B"))))))), "Every nonzero supported term has the sum of the two original input weights. The unshuffle slots partition all input positions.", DescribeRole.Theorem),
        Entry("starWord-above", "starWord_above", "starWord_above", Q("k",V("N"),Q("A",V("Word"),Q("B",V("Word"),Mem(Call("starWord",V("A"),V("B")),Call("above",V("k"),Call("level",V("k"),V("B"))))))), "Each non-k letter of B contributes at least one non-k letter in every supported output. Multiplication adds counts; summation and cancellation cannot create smaller-level support.", DescribeRole.Theorem))));
    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string s) => F.Id(s);
    private static Formula Q(string x, Formula t, Formula b) => Seq(Forall,Sp,V(x),Colon,t,Comma,b);
    private static Formula Ns(string[] xs, Formula b) { for (var i=xs.Length-1;i>=0;i--) b=Q(xs[i],V("N"),b); return b; }
    private static Formula Imp(Formula a, Formula b) => Seq(Open,a,Close,Implies,b);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Close,Land,Open,b,Close);
    private static Formula Mem(Formula a, Formula b) => Seq(a,InMacro,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a,To,b);
    private static Formula Coeff(Formula p, Formula w) => Call("coeff",p,w);
    private static Formula Tensor(Formula a, Formula b) => Call("tmulQ",a,b);
    private static Formula Pair(Formula a, Formula b) => Call("pair",a,b);
    private static Formula WB(Formula a) => Call("wordBasis",a);
    private static Formula LA(Formula a, Formula s) => Call("letterAction",a,s);
    private static Formula Sum(Formula set, string x, Formula body) => Call("sum",set,Call("lambda",V(x),body));
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
}
