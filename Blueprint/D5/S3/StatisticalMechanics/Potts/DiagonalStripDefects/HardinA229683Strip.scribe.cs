using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA229683StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229683";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical six-column two-defect arrays", H("Canonical six-column two-defect arrays"), Blocks(
        Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"),
            H("Literal row-major canonical count"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229683Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("f", Arr(Prod(Call("Fin", V("n")), Fin("6")), Fin("3")), And(Eq(Call("DefectTransfer.defects", Call("Finset.empty"), Call("HardinA229637RowColumn.betw", N("6")), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Fin("6"), App(V("f"), Pair(V("i"), V("j"))))))), N("2")), All("p", Prod(Call("Fin", V("n")), Fin("6")), All("c", Fin("3"), Imp(Lt(V("c"), App(V("f"), V("p"))), Ex("q", Prod(Call("Fin", V("n")), Fin("6")), And(Lt(Add(Mul(N("6"), Call("Fin.val", Call("Prod.fst", V("q")))), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(N("6"), Call("Fin.val", Call("Prod.fst", V("p")))), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("f"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The index counts rows. The arrays have exactly two monochromatic diagonal or antidiagonal bonds, with colours introduced in row-major order. The published sequence starts at index one. The literal filter here also defines index zero."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("counting-bridge"), DeclarationHandle.Create(Prefix + "counting_bridge"),
            H("Labelled transfer and canonical count"), StatementSource.FromAuthor(Disp(All("m", V("Nat"), Eq(Call("dotProduct", Call("HardinA229683StripData.initial"), Call("Matrix.mulVec", Power(Call("HardinA229683StripData.T"), V("m")), Call("HardinA229683StripData.terminal"))), Mul(N("6"), CastInt(Call("HardinA229683Strip.a", Add(V("m"), N("1"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The transfer counts labelled arrays at budget two. Constant arrays have a multiple of ten defects, so each canonical array at budget two has six labelled realizations. For a single row both counts vanish."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
            H("Order-eighteen recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("21")))), Sub(Add(Sub(Add(Add(Sub(Sub(Add(Sub(Sub(Add(Add(Sub(Add(Add(Sub(Mul(N("75"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("20"))))), Mul(N("2010"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("19")))))), Mul(N("19486"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("18")))))), Mul(N("60075"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("17")))))), Mul(N("2206575"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("16")))))), Mul(N("7404210"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("15")))))), Mul(N("70536825"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("14")))))), Mul(N("435322350"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("13")))))), Mul(N("601275555"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("12")))))), Mul(N("8082823950"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("11")))))), Mul(N("6257717775"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("10")))))), Mul(N("54520532190"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("9")))))), Mul(N("92909172825"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("8")))))), Mul(N("132368667075"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("7")))))), Mul(N("366499782594"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("6")))))), Mul(N("470715894135"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("4")))))), Mul(N("282429536481"), CastInt(Call("HardinA229683Strip.a", Add(V("n"), N("3")))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The forward relation propagates under further transfer steps and gives the recurrence at all indices at least twenty-one."))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229683"), ResolutionKind.Proved)))));
    private static Formula N(string digits, bool negative = false) => negative ? Seq(Neg, Sp, N(digits)) :
        D(digits.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(part))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula Call(string s, params Formula[] xs) => xs.Length == 0 ? Q(s) : App(Q(s), xs);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Prod(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula CastInt(Formula a) => Typed(a, V("Int"));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula Fin(string n) => Call("Fin", N(n));
}
