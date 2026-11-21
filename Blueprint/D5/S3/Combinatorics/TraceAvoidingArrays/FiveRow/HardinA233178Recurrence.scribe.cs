using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow;

internal sealed class HardinA233178RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-width recurrence for the literal normalized six-colour five-row array count.",
        H("From exact source cardinalities to the full recurrence"), Blocks(
            Paragraph(Text("The source count and FullE are those of HardinA233178Literal. "
                + "The transfer uses the original five rows as five independent base-three digits. "
                + "Its three-label columns are an auxiliary representation of the source graph. "
                + "No continuation or source-correspondence hypothesis is assumed.")),
            FormulaNode("columnEquiv", ColumnEquiv(), false, "A ternary code is equivalent to a function assigning a label to each of the five rows."),
            FormulaNode("count_transfer", CountTransfer(), true,
                "The base-three equivalence identifies arrays with sequences of column codes. "
                + "The literal edges impose Bond on consecutive codes. TransferMatrix.cont_matrix "
                + "counts the continuations from each initial column, and the dot product sums over those columns."),
            FormulaNode("chromatic_recurrence", ChromaticRecurrence(), true,
                "The continuation recurrence applied to the constant-one vector gives the recurrence for the chromatic count."),
            FormulaNode("result", SourceRecurrence(), true,
                "The chromatic coefficients sum to one, so adding six preserves the unscaled "
                + "recurrence. Substitution of 48*a(n)=32^n*(chromaticCount(n)+6) multiplies "
                + "the coefficient at lag i by 32^i. All lag widths are at least two when the "
                + "source width exceeds eleven.",
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Automata/hardin2013a233178")),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233178"), ResolutionKind.Proved)))));

    private static DocumentBlock FormulaNode(string name, Formula statement, bool theorem, string prose,
        AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition, resolution);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(long c, Formula a) => new Formula.Binary(N(c), FormulaBinaryOperator.Multiply, a);
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), t), Comma, Sp, Parenthesized(body));

    private static Formula ColumnEquiv()
    {
        var functions = Arrow(Fin(5), Fin(3));
        var codes = Call("Fin", Seq(N(3), Caret, Grp(N(5))));
        return Eq(Typed(Q("HardinA233178Recurrence.columnEquiv"), Call("Equiv", Column(), functions)),
            Call("Equiv.symm", Typed(Q("finFunctionFinEquiv"), Call("Equiv", functions, codes))));
    }

    private static Formula CountAt(int shift) =>
        Call("HardinA233178Literal.chromaticCount", Add(V("n"), N(shift)));

    private static Formula CountTransfer() => All("n", Q("Nat"), Eq(CountAt(1),
        Call("dotProduct", Typed(N(1), Arrow(Column(), Q("Int"))), Call("HardinA233178Chromatic.v", V("n")))));

    private static Formula ChromaticRecurrence()
    {
        var rhs = Add(Mul(6, CountAt(11)), Mul(31, CountAt(10)));
        rhs = Sub(Sub(rhs, Mul(97, CountAt(9))), Mul(163, CountAt(8)));
        rhs = Add(Add(rhs, Mul(417, CountAt(7))), Mul(93, CountAt(6)));
        rhs = Add(Sub(rhs, Mul(514, CountAt(5))), Mul(192, CountAt(4)));
        rhs = Sub(Add(rhs, Mul(72, CountAt(3))), Mul(36, CountAt(2)));
        return All("n", Q("Nat"), Eq(CountAt(12), rhs));
    }

    private static Formula SourceRecurrence()
    {
        Formula A(Formula width) => Typed(Call("HardinA233178Literal.a", width), Q("Int"));
        Formula Lag(int shift) => A(Sub(V("n"), N(shift)));
        var rhs = Add(Mul(192, Lag(1)), Mul(31744, Lag(2)));
        rhs = Sub(Sub(rhs, Mul(3178496, Lag(3))), Mul(170917888, Lag(4)));
        rhs = Add(Add(rhs, Mul(13992198144, Lag(5))), Mul(99857989632, Lag(6)));
        rhs = Add(Sub(rhs, Mul(17660905521152, Lag(7))), Mul(211106232532992, Lag(8)));
        rhs = Sub(Add(rhs, Mul(2533274790395904, Lag(9))), Mul(40532396646334464, Lag(10)));
        var onset = new Formula.Relation(N(11), FormulaRelationOperator.LessThan, V("n"));
        return All("n", Q("Nat"), new Formula.Logic(onset, FormulaLogicOperator.Implies, Eq(A(V("n")), rhs)));
    }
}
