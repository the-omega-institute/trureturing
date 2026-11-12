using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RichWordRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/RichWordRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform recurrence and absence of every positive eventual tail period for the actual seven-letter source and its literal four-letter image.",
        H("Recurrence and Tail Periods of the Literal Rich Words"), Blocks(
            Paragraph(Text("The source u is RichWordTypeIOccurrence.word on Fin 7, the fixed point of the literal substitution i -> 0(i+1) for i < 6 and 6 -> 066. The output x is RichWordOutputDecoder.x on Fin 4 with dictionary (a,ab,abb,ac,acc,accdcc,accdccddccdcc). The notation factor(y,i,n) denotes the length-n window beginning at i. All positions are natural numbers, including zero; empty windows and overlapping occurrences are included.")),
            Entry("source_uniform_recurrence", "source-recurrence", "All source factors recur uniformly", Recurrence("u"),
                "For each source window there is one bound B that works for every starting position q. The repeated window lies wholly inside [q,q+B). An iterate prefix containing the given factor is a prefix of every source block one level deeper, because every substitution image begins with zero. The actual iterated cuts partition the source, and each block at depth k has length at most 3^k. Taking the next cut supplies the uniform window bound."),
            Entry("source_no_tail", "source-tail", "The source has no eventual positive period", NoTail("u"),
                "EventuallyPeriodicWord(y) means that there exist natural numbers s and p with p > 0 and y(s+t+p)=y(s+t) for every natural t. Type-I factors have unbounded lengths and two distinct actual right extensions, phase(n) and 6. Uniform recurrence places both extended factors beyond any proposed preperiod. In a tail of period p, equality of a factor of length at least p forces equality of its following letter, contradicting those two extensions."),
            Entry("output_uniform_recurrence", "output-recurrence", "All output factors recur uniformly", Recurrence("x"),
                "The bound applies to arbitrary output windows, including windows crossing image boundaries. Enclose the window in the image of a finite source block and retain its offset from that block's first marker. Source recurrence repeats the whole block. Every code word has length between 1 and 13, so bounded source gaps give bounded output gaps. Repeating the same offset reproduces the original output factor."),
            Entry("output_no_tail", "output-tail", "The literal output has no eventual positive period", NoTail("x"),
                "The exact marker inverse identifies every output marker with one source boundary. Translating a sufficiently late marker by a proposed output period sends consecutive markers to consecutive markers: an intervening marker would translate back to an intervening original boundary. Thus translation induces a fixed positive displacement of source indices. The marked-core reconstruction identifies each translated source letter, giving a positive eventual source period and a contradiction."),
            Paragraph(Text("These results concern recurrence and eventual periods of these precise words. The ordinary critical exponent, the full bispecial classification, richness, scalar spectral inequalities, and remaining parent clauses require their separate arguments.")))));

    private static DocumentBlock Entry(string name, string id, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix+name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [..args]);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string v, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), N(), body);
    private static Formula Ex(string v, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), N(), body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Recurrence(string name)
    {
        Formula i=F.Id("i"), n=F.Id("n"), b=F.Id("B"), q=F.Id("q"), j=F.Id("j"), y=C(name);
        return All("i", All("n", Ex("B", All("q", Ex("j",
            And(Le(q,j), And(Le(Add(j,n),Add(q,b)), Eq(C("factor",y,j,n),C("factor",y,i,n)))))))));
    }
    private static Formula NoTail(string name) => Seq(Neg, Sp, C("EventuallyPeriodicWord", C(name)));
}
