using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class SubstitutionPrefixEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/SubstitutionPrefixEnvelope.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete block charges control all prefixes of iterated substitutions and their intervals.",
        H("Alternating Charges of Substitution Prefixes"),
        Blocks(
            Paragraph(Text("Let alpha be any alphabet, w an integer weight and f a list-valued substitution. No finiteness of the alphabet, nonerasing condition or parity hypothesis is imposed. image f j a is the actual jth iterate, with the zero iterate [a]. Alternation starts positively at the beginning of each list. A change of starting phase multiplies the charge by a power of -1 and therefore preserves its absolute value.")),
            Node("charge", "charge", "Local alternating charge", DescribeRole.Definition,
                All("alpha", V("Type"), All("w", Arrow(V("alpha"), Int()),
                    All("v", Call("List", V("alpha")), Eq(Call("charge", V("w"), V("v")),
                        Call("alternatingSum", Call("map", V("w"), V("v"))))))),
                "The empty charge is zero. For concatenation uv, the charge is Q(u)+(-1)^length(u) Q(v). Consequently its absolute value is at most |Q(u)|+|Q(v)|, regardless of whether either length is odd."),
            Node("prefix_envelope", "prefix-envelope", "The recursive prefix estimate", DescribeRole.Theorem,
                Parameters(All("j", Nat(), All("a", V("alpha"), All("t", Nat(),
                    Le(Abs(Call("charge", V("w"), Call("take", V("t"), Image(V("a"))))), Envelope()))))),
                "Assume M>=0, every |w(a)|<=M, length(f(a))<=B, every H(j)>=0 and every complete jth image has charge at most H(j) in absolute value. Then every take index t satisfies the displayed bound. Here sum(range(j),H) means the sum of H(i) over 0<=i<j. This includes t=0, whole prefixes, indices beyond the end and empty images. Locate the endpoint in the concatenation of level-j children using exists_flatMap_block. Before that endpoint are at most B complete children; the remaining child contributes its recursively controlled prefix. The base image is a singleton. This induction establishes prefix control from complete-block control at all levels."),
            Node("two_block_interval_bound", "two-block-interval", "Intervals in two adjacent images", DescribeRole.Theorem,
                Parameters(All("j", Nat(), All("a", V("alpha"), All("b", V("alpha"),
                    All("v", Call("List", V("alpha")), Imp(Call("infix", V("v"),
                        Call("append", Image(V("a")), Image(V("b")))),
                        Le(Abs(Call("charge", V("w"), V("v"))), Mul(D(4), Envelope())))))))),
                "Under the same hypotheses, every infix of the concatenation of any two jth images has charge at most four times the prefix envelope. Every prefix of this concatenation has charge at most twice the envelope. Subtracting the charge of the prefix preceding the interval, with its exact alternating phase, gives the interval bound. The letters may coincide and the interval may be empty. There is no asserted occurrence in any infinite word."))));

    private static Formula Parameters(Formula body)
    {
        Formula assumptions = And(Le(D(0), V("M")),
            All("a", V("alpha"), Le(Abs(Call("w", V("a"))), V("M"))),
            All("a", V("alpha"), Le(Call("length", Call("f", V("a"))), V("B"))),
            All("j", Nat(), Le(D(0), Call("H", V("j")))),
            All("j", Nat(), All("a", V("alpha"), Le(Abs(Call("charge", V("w"), Image(V("a")))), Call("H", V("j"))))));
        return All("alpha", V("Type"), All("w", Arrow(V("alpha"), Int()),
            All("f", Arrow(V("alpha"), Call("List", V("alpha"))),
            All("M", Int(), All("B", Nat(), All("H", Arrow(Nat(), Int()), Imp(assumptions, body)))))));
    }
    private static Formula Image(Formula a) => Call("image", V("f"), V("j"), a);
    private static Formula Envelope() => Add(V("M"), Mul(V("B"), Call("sum", Call("range", V("j")), V("H"))));
    private static DocumentBlock Node(string name, string id, string title, DescribeRole role, Formula statement, string prose) => Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix+name), H(title), StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => F.Seq(F.Mathbb, F.Grp(V("N")));
    private static Formula Int() => F.Seq(F.Mathbb, F.Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => F.Seq(a, F.Sp, F.To, F.Sp, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Abs(Formula a) => Call("abs", a);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] xs) { Formula r=xs[^1]; for(int i=xs.Length-2;i>=0;--i) r=new Formula.Logic(xs[i],FormulaLogicOperator.And,r); return r; }
}
