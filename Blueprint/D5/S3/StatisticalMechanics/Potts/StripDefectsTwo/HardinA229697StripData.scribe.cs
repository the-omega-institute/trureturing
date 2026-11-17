using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo;
internal sealed class HardinA229697StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.";
    private const string Note="D5/L/SpinModels/hardin2013a229697";
    private const string DataName="HardinA229697StripData";
    private const string OldName="HardinA229589StripData";
    private const int Rows=4;
    private const int States=42;
    private const int Last=17;
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect sheared square-lattice strip counts.",H("Two-defect HA strips"),Blocks(
        Describe.Lean(DescribeId.Create("valid"),DeclarationHandle.Create(Prefix+"Valid"),H("Valid"),StatementSource.FromAuthor(Disp(All("p",Row(),All("d",V("Nat"),Iff(Valid(V("p"),V("d")),Leq(V("d"),Num(2))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Residual budgets are at most two."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("cl"),DeclarationHandle.Create(Prefix+"cl"),H("cl"),StatementSource.FromAuthor(Disp(All("p",Row(),All("d",V("Nat"),Eq(Cl(V("p"),V("d")),If(Lt(Num(0),V("d")),Typed(Call("Fin.castAdd",Num(14),Old("cl",V("p"),Sub(V("d"),Num(1)))),Fin(States)),Typed(Call("Fin.natAdd",Num(28),Call("HardinA233177PairTransfer.cls",Parenthesized(Seq(App(V("p"),Typed(Num(0),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(1),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(2),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(3),Fin(Rows))))))),Fin(States)))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Positive budgets call the frozen one-defect classifier at d minus one. Zero budget selects the appended equality sector."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("t"),DeclarationHandle.Create(Prefix+"T"),H("T"),StatementSource.FromAuthor(Disp(Typed(Data("T"),Call("Matrix",Fin(States),Fin(States),V("Int"))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 42 by 42 integer matrix retains HardinA229589StripData.T in its leading 28 by 28 block. The added block records cost two and the inherited cost-one block; its diagonal is the frozen zero-temperature Q. The HardinA229697Strip.finite_certificate theorem pins every transition sum."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("initial"),DeclarationHandle.Create(Prefix+"initial"),H("initial"),StatementSource.FromAuthor(Disp(Typed(Data("initial"),new Formula.TypeArrow(Fin(States),V("Int"))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 42 integer initial weights append 14 zero entries to the frozen initial vector; HardinA229697Strip.finite_certificate pins the initial class counts."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("terminal"),DeclarationHandle.Create(Prefix+"terminal"),H("terminal"),StatementSource.FromAuthor(Disp(Typed(Data("terminal"),new Formula.TypeArrow(Fin(States),V("Int"))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 42 integer acceptance weights are zero on the leading 28 states and one on the final 14 states; HardinA229697Strip.finite_certificate pins acceptance at residual zero."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("w"),DeclarationHandle.Create(Prefix+"W"),H("W"),StatementSource.FromAuthor(Disp(Typed(Data("W"),new Formula.TypeArrow(Fin(Last+1),new Formula.TypeArrow(Fin(States),V("Int")))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 18 by 42 integer table appends the new sector to the first 13 cached rows of HardinA229589StripData.W, then tabulates the remaining rows. HardinA229697StripForward.forward_certificate pins its initial row, every successor row, and its polynomial relation."))),DescribeRole.Definition))));

    private static Formula Num(int n) => n < 0 ? Parenthesized(Seq(Minus, Num(-n))) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c-'0')).ToArray());
    private static Formula V(string n) => new Formula.Symbol(FormulaIdentifier.Create(n));
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i) => i == 0 ? new[] { Seq(Operatorname, Grp(V(p))) } : new[] { Dot, Seq(Operatorname, Grp(V(p))) }).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length == 0 ? Q(n) : new Formula.Apply(Q(n), [..a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Fin(int n) => Call("Fin",Num(n));
    private static Formula Row() => new Formula.TypeArrow(Fin(Rows),Fin(3));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Land,Sp,Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a),Sp,F.Iff,Sp,Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n, params Formula[] a) => Call(DataName+"."+n,a);
    private static Formula Old(string n, params Formula[] a) => Call(OldName+"."+n,a);
    private static Formula Valid(Formula p, Formula d) => Data("Valid",p,d);
    private static Formula Cl(Formula p, Formula d) => Data("cl",p,d);
    private static Formula Join(params Formula[] a) => a.Length==1 ? a[0] : And(a[0],Join(a.Skip(1).ToArray()));
}
