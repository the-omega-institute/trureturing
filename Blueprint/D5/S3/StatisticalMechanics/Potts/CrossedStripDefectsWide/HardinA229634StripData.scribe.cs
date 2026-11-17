using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide;
internal sealed class HardinA229634StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229634";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-budget HDA extension.", H("Width-five two-defect transfer"), Blocks(
            Describe.Lean(DescribeId.Create("valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Residual-budget invariant"), StatementSource.FromAuthor(Disp(All("p", RowType(), All("d", Call("Nat"), Eq(Call("HardinA229634StripData.Valid", V("p"), V("d")), Parenthesized(And(Le(V("d"), Num("2")), Le(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), V("p"), V("p")), Sub(Num("2"), V("d")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The row and natural residual budget satisfy d at most two and horizontal defects at most two minus d; subtraction is truncated natural subtraction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("Class map"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229634StripData.cl"), new Formula.TypeArrow(RowType(), new Formula.TypeArrow(Call("Nat"), Fin(33)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The function retains HardinA229531StripData.cl at positive residual budget, subtracts one from the budget and embeds Fin 20 into Fin 33. At zero residual it appends thirteen classes: six proper classes followed by seven classes of identical zero-cost successor counts. The equality code sums powers of two for the ten equal-position predicates. Membership in each finite code set selects a class. Nat.mod denotes the nonnegative remainder modulo six. HardinA229634StripClasses.transition_counts pins every class against actual rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
                H("Block extension"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229634StripData.T"), Call("Matrix", Fin(33), Fin(33), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 33 by 33 integer matrix is reindexed from a 20 plus 13 block matrix. Its upper left block is exactly HardinA229531StripData.T and its lower left block is zero. The six proper rows of the new lower right block use the frozen terminal proper block at indices six through eleven. All appended entries are pinned by HardinA229634StripClasses.transition_counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("Initial distribution"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229634StripData.initial"), new Formula.TypeArrow(Fin(33), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Fin.append retains HardinA229531StripData.initial and appends thirteen weights counting initial rows with two horizontal defects. The literal initial-row sum is checked in HardinA229634Strip.finite_certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
                H("Terminal indicator"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229634StripData.terminal"), new Formula.TypeArrow(Fin(33), Call("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first twenty entries are zero and the appended thirteen entries are one. The finite certificate identifies this with zero residual budget for every valid row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
                H("Forward vectors"), StatementSource.FromAuthor(Disp(Typed(Call("HardinA229634StripData.W"), new Formula.TypeArrow(Fin(21), new Formula.TypeArrow(Fin(33), Call("Int")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The 21 by 33 integer table keeps all fourteen available forward rows from HardinA229531StripData.W in the inherited block. The remaining entries are explicit integers. HardinA229634Strip.finite_certificate pins row zero to initial, all twenty matrix steps, and the order-eighteen relation at row twenty."))), DescribeRole.Definition))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(string value) => D(value.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(new Formula.Symbol(FormulaIdentifier.Create(part)))) }
        : new[] { Dot, Seq(Operatorname, Grp(new Formula.Symbol(FormulaIdentifier.Create(part)))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : new Formula.Apply(Q(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(int size) => Call("Fin", Num(size.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula RowType() => new Formula.TypeArrow(Fin(5), Fin(3));
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
}
