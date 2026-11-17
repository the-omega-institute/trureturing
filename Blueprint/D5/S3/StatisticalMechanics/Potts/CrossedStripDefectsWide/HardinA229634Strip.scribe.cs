using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide;
internal sealed class HardinA229634StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229634";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal HDA colourings and exact defect transfer.", H("Hardin A229531: exact defect recurrence"),
        Blocks(Paragraph(Text("The literal array has n rows, 5 columns and exactly two monochromatic HDA bond. Rows are swept by an exact-budget transfer with 33 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. Finite certificates check the exact image and every defect entry.")),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"), H("The literal canonical array count"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229634Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("A", Arrow(Product(Call("Fin", V("n")), Call("Fin", Num("5"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA229531StripData.horizontal"), Call("HardinA229531StripData.between"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Call("Fin", Num("5")), App(V("A"), Pair(V("i"), V("j"))))))), Num("2")), All("p", Product(Call("Fin", V("n")), Call("Fin", Num("5"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("A"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Call("Fin", Num("5"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("A"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The registered all-index recurrence"), StatementSource.FromAuthor(Disp(RecurrenceFormula())),

                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The recurrence is an identity in the integers at every index at least 21. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim."))), DescribeRole.Theorem))));

    private static Formula RecurrenceFormula()
    {
        int[] coefficients = [42, -723, 6569, -33687, 94839, -116010, -55215, 305043,
            -230994, -118011, 243513, -84933, -40719, 42804, -14887, 2598, -228, 8];
        Formula Term(int i) => Mul(Num((coefficients[i] < 0 ? -coefficients[i] : coefficients[i]).ToString(System.Globalization.CultureInfo.InvariantCulture)),
            AsInt(Call("HardinA229634Strip.a", Add(V("n"), Num((20-i).ToString(System.Globalization.CultureInfo.InvariantCulture))))));
        Formula rhs = Term(0);
        for (int i = 1; i < coefficients.Length; i++) rhs = coefficients[i] < 0 ? Sub(rhs, Term(i)) : Add(rhs, Term(i));
        return All("n", Call("Nat"), Eq(AsInt(Call("HardinA229634Strip.a", Add(V("n"), Num("21")))), rhs));
    }
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
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));

    private static Formula AsInt(Formula value) => Parenthesized(Seq(value, Colon, Sp, Call("Int")));

}
