using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo;
internal sealed class HardinA229697StripClasses0Document : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripClasses0.";
    private const string Note="D5/L/SpinModels/hardin2013a229697";
    private const string DataName="HardinA229697StripData";
    private const string OldName="HardinA229589StripData";
    private const int Rows=4;
    private const int States=42;
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect sheared square-lattice strip counts.",H("Two-defect HA strips"),Blocks(
        Describe.Lean(DescribeId.Create("transition-counts"),DeclarationHandle.Create(Prefix+"transition_counts"),H("transition_counts"),StatementSource.FromAuthor(Disp(All("j",Fin(14),Imp(And(Leq(Num(0),Val(V("j"))),Lt(Val(V("j")),Num(2))),All("p",Row(),Transition(V("p"),Num(2),Typed(Call("Fin.natAdd",Num(28),V("j")),Fin(States)))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Counts only the new cost-two transitions into the stated output interval. The sum runs over every actual successor column with three possible colours at each site."))),DescribeRole.Theorem))));

    private static Formula Num(int n) => n < 0 ? Parenthesized(Seq(Minus, Num(-n))) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c-'0')).ToArray());
    private static Formula V(string n) => new Formula.Symbol(FormulaIdentifier.Create(n));
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i) => i == 0 ? new[] { Seq(Operatorname, Grp(V(p))) } : new[] { Dot, Seq(Operatorname, Grp(V(p))) }).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length == 0 ? Q(n) : new Formula.Apply(Q(n), [..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Fin(int n) => Call("Fin",Num(n));
    private static Formula Row() => new Formula.TypeArrow(Fin(Rows),Fin(3));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Parenthesized(b));
    private static Formula Sum(string n, Formula t, Formula b) => Seq(F.Sum,Underscore,Grp(V(n),Colon,Sp,t),Sp,Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Land,Sp,Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Implies,Sp,Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n, params Formula[] a) => Call(DataName+"."+n,a);
    private static Formula Old(string n, params Formula[] a) => Call(OldName+"."+n,a);
    private static Formula Cost(Formula p, Formula r) => Add(Call("DefectTransfer.bondDefects",Old("between"),p,r),Call("DefectTransfer.bondDefects",Old("horizontal"),r,r));
    private static Formula Cl(Formula p, Formula d) => Data("cl",p,d);
    private static Formula Transition(Formula p, Formula d, Formula s) => Eq(Sum("r",Row(),If(And(Leq(Cost(p,V("r")),d),Eq(Cl(V("r"),Sub(d,Parenthesized(Cost(p,V("r"))))),s)),Typed(Num(1),V("Int")),Typed(Num(0),V("Int")))),Data("T",Cl(p,d),s));
    private static Formula Join(params Formula[] a) => a.Length==1 ? a[0] : And(a[0],Join(a.Skip(1).ToArray()));
}
