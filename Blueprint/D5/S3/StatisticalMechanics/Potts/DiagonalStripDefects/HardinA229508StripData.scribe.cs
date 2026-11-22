using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA229508StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229508";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-defect sectors of the six-column transfer", H("One-defect sectors of the six-column transfer"), Blocks(
        Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
            H("Remaining budget and boundary class"), StatementSource.FromAuthor(Disp(All("p", Row("6"), All("d", V("Nat"), Eq(Typed(Call("HardinA229508StripData.cl", V("p"), V("d")), Call("Sum", Fin("15"), Fin("15"))), If(Eq(V("d"), N("0")), Call("Sum.inr", Call("HardinA203981StripData.boundary", V("p"))), Call("Sum.inl", Call("HardinA203981StripData.boundary", V("p"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The first sector still permits one defect. The second sector has spent its budget."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("half-one"), DeclarationHandle.Create(Prefix + "halfOne"),
            H("The half-strip block with reversed targets"), StatementSource.FromAuthor(Disp(All("i", Fin("5"), All("j", Fin("5"), Eq(Call("HardinA229508StripData.halfOne", V("i"), V("j")),
                Call("HardinA229588Strip.T", Call("Fin.castAdd", N("5"), V("i")),
                    Call("Fin.natAdd", N("5"), Call("Equiv.swap", N("1"), N("3"), V("j"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The row starts with budget 1. The column has zero remaining budget and uses the reversed triple class."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("costone"), DeclarationHandle.Create(Prefix + "costOne"),
            H("The exact-one-defect matrix"), StatementSource.FromAuthor(Disp(CostFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Each summand counts one allocation of the exact defect cost between the two parity classes."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
            H("One-defect transfer matrix"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA229508StripData.T"), Call("Matrix", Call("Sum", Fin("15"), Fin("15")), Call("Sum", Fin("15"), Fin("15")), V("Int"))), Call("Matrix.fromBlocks", Call("HardinA203981StripData.T"), Call("HardinA229508StripData.costOne"), Typed(N("0"), Call("Matrix", Fin("15"), Fin("15"), V("Int"))), Call("HardinA203981StripData.T"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The diagonal blocks preserve the remaining budget. The upper-right block spends it."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
            H("Weights at the first labelled row"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA229508StripData.initial"), Arr(Call("Sum", Fin("15"), Fin("15")), V("Int"))), Call("Sum.elim", Call("HardinA203981StripData.initial"), Typed(N("0"), Arr(Fin("15"), V("Int"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The entire budget remains at the first row, with no within-row bonds."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
            H("Weights for exhausting the budget"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA229508StripData.terminal"), Arr(Call("Sum", Fin("15"), Fin("15")), V("Int"))), Call("Sum.elim", Typed(N("0"), Arr(Fin("15"), V("Int"))), Typed(N("1"), Arr(Fin("15"), V("Int"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only the zero-remaining-budget sector contributes to the count."))), DescribeRole.Definition))));
    private static Formula CostFormula()
    {
        var i = V("i"); var j = V("j");
        Formula Product(string a, string b) =>
            Call("HardinA203981StripData.classProduct", Call(a), Call(b), i, j);
        return All("i", Fin("15"), All("j", Fin("15"), Eq(Call("HardinA229508StripData.costOne", i, j),
            Add(Product("HardinA203981StripData.halfZero", "HardinA229508StripData.halfOne"), Product("HardinA229508StripData.halfOne", "HardinA203981StripData.halfZero")))));
    }

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

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
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fin(string n) => Call("Fin", N(n));
    private static Formula Row(string n) => Arr(Fin(n), Fin("3"));
    private static Formula If(Formula c, Formula y, Formula n) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
}
