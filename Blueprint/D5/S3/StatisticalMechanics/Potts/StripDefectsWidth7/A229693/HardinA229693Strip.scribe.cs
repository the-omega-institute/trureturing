using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693;

internal sealed class HardinA229693StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229693";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The width-seven two-defect recurrence.", H("The width-seven two-defect recurrence"),
        Blocks(
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("First-row weights"),
                StatementSource.FromAuthor(Disp(InitialFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first 72 entries are the A229585 initial weights. The remaining entries count labelled rows with exactly two horizontal defects, grouped by exhausted boundary class. The strip counting formula uses this vector on the left."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("Acceptance weights"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229693Strip.terminal"), Call("Fin.append", TypeOf(Num("0"), Arrow(Call("Fin", Num("72")), V("Int"))), TypeOf(Num("1"), Arrow(Call("Fin", Num("96")), V("Int"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A completed strip is accepted when its remaining budget is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count-transfer"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.count_transfer"), H("The labelled strip count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("DefectTransfer.literalCount", Parenthesized(Seq(V("q"), Sp, Colon, F.Eq, Sp, Num("3"))), Call("HardinA229585StripData.horizontal"), Call("HardinA229585StripData.antidiagonal"), Num("2"), Add(V("n"), Num("1")))), Call("dotProduct", Call("HardinA229693Strip.initial"), Call("Matrix.mulVec", Power(Call("HardinA229693StripTransfer.T"), V("n")), Call("HardinA229693Strip.terminal"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first row contributes the initial weight. Each later row multiplies by the transfer matrix, and terminal weights require exact exhaustion. The empty strip has zero colourings with exactly two defects, whereas the zero-power matrix coefficient counts the positive number of qualifying one-row strips."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("Literal array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229693Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("f", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("7"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229585StripData.horizontal"), Call("HardinA229585StripData.antidiagonal"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("7")), App(V("f"), Pair(V("i"), V("j"))))))), Num("2")), Call("HardinA229585Strip.Normal", V("f")))), Call("Finset.univ"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite filter ranges over all three-colour arrays. The condition inherited from A229585 orders colour introductions by row and then by column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("Integer recurrence"),
                StatementSource.FromAuthor(Disp(All("t", V("Nat"), Eq(CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("15")))), Sub(Add(Sub(Add(Sub(Add(Sub(Add(Sub(Add(Sub(Mul(Num("126"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("14"))))), Mul(Num("6345"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("13")))))), Mul(Num("165456"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("12")))))), Mul(Num("2474469"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("11")))))), Mul(Num("22918302"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("10")))))), Mul(Num("138045627"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("9")))))), Mul(Num("554666940"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("8")))))), Mul(Num("1494608922"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("7")))))), Mul(Num("2659094568"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("6")))))), Mul(Num("2986698420"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("5")))))), Mul(Num("1913187600"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("4")))))), Mul(Num("531441000"), CastInt(Call("HardinA229693Strip.a", Add(V("t"), Num("3")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("All array counts in this equality are cast to integers. At least two colours occur in a nonempty array with two monochromatic bonds. Relabelling gives six labelled arrays per canonical array. The vector identity for the transfer at fourteen steps propagates to later steps by right multiplication.")),
                    Paragraph(Text("For every table p of fifteen integer row vectors indexed by Fin 168, assume that p at zero is the initial vector and that for every j in Fin 14, the row at j.succ is the product of the row at j.castSucc with T. Induction then identifies the row at every i in Fin 15 with forward iteration from the initial vector for i.val steps."))), DescribeRole.Theorem))));

    private static Formula InitialFormula()
    {
        var i = V("i");
        var k = V("k");
        var leading = Call("HardinA229585StripData.initial");
        var embedded = Call("oldZeroImage", Call("HardinA229585StripData.zeroBudgetClass", k));
        var zero = Seq(Exists, Sp, k, Colon, Sp, Call("Fin", Num("16")), Comma, Sp,
            Parenthesized(Eq(i, embedded)));
        var suffix = Conditional(Lt(Call("Fin.val", i), Num("56")),
            Conditional(zero, CastInt(Num("0")), CastInt(Num("6"))), CastInt(Num("12")));
        return Eq(Call("HardinA229693Strip.initial"),
            Call("Fin.append", leading, Fn("i", Call("Fin", Num("96")), suffix)));
    }

    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Conditional(Formula p, Formula y, Formula n) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(p), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula TypeOf(Formula a, Formula b) => Seq(a, Sp, Colon, Sp, b);
    private static Formula Power(Formula a, Formula b) => Seq(Parenthesized(a), Caret, Grp(b));
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));

}
