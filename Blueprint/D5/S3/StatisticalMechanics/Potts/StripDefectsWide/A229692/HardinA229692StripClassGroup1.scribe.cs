using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229692;
internal sealed class HardinA229692StripClassGroup1Document : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229692/HardinA229692StripClassGroup1.";
    private const string Note="D5/L/SpinModels/hardin2013a229692";
    private const string DataName="HardinA229692StripData",OldName="HardinA229584StripData";
    private const int Rows=6;
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect six-column sheared square-lattice counts.",H("Two-defect HA strips"),Blocks(
        Describe.Lean(DescribeId.Create("transition-counts6"),DeclarationHandle.Create(Prefix+"transition_counts6"),H("transition_counts6"),
            StatementSource.FromAuthor(Disp(All("p",Boundary(),All("d",Fin(3),Imp(Data("Valid",V("p"),Val(V("d"))),Imp(Call("HardinA233177Canonical.Canonical",V("p")),Imp(Not(And(Leq(Val(V("d")),Num(1)),Old("Valid",V("p"),Val(V("d"))))),Transition(V("p"),Val(V("d")),Typed(Num(38),Fin(68)))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts7"),DeclarationHandle.Create(Prefix+"transition_counts7"),H("transition_counts7"),
            StatementSource.FromAuthor(Disp(All("p",Boundary(),All("d",Fin(3),Imp(Data("Valid",V("p"),Val(V("d"))),Imp(Call("HardinA233177Canonical.Canonical",V("p")),Imp(Not(And(Leq(Val(V("d")),Num(1)),Old("Valid",V("p"),Val(V("d"))))),Transition(V("p"),Val(V("d")),Typed(Num(39),Fin(68)))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts8"),DeclarationHandle.Create(Prefix+"transition_counts8"),H("transition_counts8"),
            StatementSource.FromAuthor(Disp(All("p",Boundary(),All("d",Fin(3),Imp(Data("Valid",V("p"),Val(V("d"))),Imp(Call("HardinA233177Canonical.Canonical",V("p")),Imp(Not(And(Leq(Val(V("d")),Num(1)),Old("Valid",V("p"),Val(V("d"))))),Transition(V("p"),Val(V("d")),Typed(Num(40),Fin(68)))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts9"),DeclarationHandle.Create(Prefix+"transition_counts9"),H("transition_counts9"),
            StatementSource.FromAuthor(Disp(All("p",Boundary(),All("d",Fin(3),Imp(Data("Valid",V("p"),Val(V("d"))),Imp(Call("HardinA233177Canonical.Canonical",V("p")),Imp(Not(And(Leq(Val(V("d")),Num(1)),Old("Valid",V("p"),Val(V("d"))))),Transition(V("p"),Val(V("d")),Typed(Num(41),Fin(68)))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts10"),DeclarationHandle.Create(Prefix+"transition_counts10"),H("transition_counts10"),
            StatementSource.FromAuthor(Disp(All("p",Boundary(),All("d",Fin(3),Imp(Data("Valid",V("p"),Val(V("d"))),Imp(Call("HardinA233177Canonical.Canonical",V("p")),Imp(Not(And(Leq(Val(V("d")),Num(1)),Old("Valid",V("p"),Val(V("d"))))),Transition(V("p"),Val(V("d")),Typed(Num(42),Fin(68)))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts11"),DeclarationHandle.Create(Prefix+"transition_counts11"),H("transition_counts11"),
            StatementSource.FromAuthor(Disp(All("p",Boundary(),All("d",Fin(3),Imp(Data("Valid",V("p"),Val(V("d"))),Imp(Call("HardinA233177Canonical.Canonical",V("p")),Imp(Not(And(Leq(Val(V("d")),Num(1)),Old("Valid",V("p"),Val(V("d"))))),Transition(V("p"),Val(V("d")),Typed(Num(43),Fin(68)))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Only new-sector canonical boundaries are enumerated; the old valid domain is excluded by the explicit hypothesis."))),DescribeRole.Theorem))));

    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus, Num(-n))) : new Formula.Number(n);
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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Land,Sp,Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg,Parenthesized(a));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Implies,Sp,Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n, params Formula[] a) => Call(DataName+"."+n,a);
    private static Formula Old(string n, params Formula[] a) => Call(OldName+"."+n,a);
    private static Formula Boundary() => new Formula.TypeArrow(Fin(5),Fin(3));
    private static Formula Cost(Formula p, Formula r) => Add(Old("cross",p,r),Call("DefectTransfer.bondDefects",Old("horizontal"),r,r));
    private static Formula Cl(Formula p, Formula d) => Data("cl",p,d);
    private static Formula Transition(Formula p, Formula d, Formula s) => Eq(Sum("r",Row(),If(And(Leq(Cost(p,V("r")),d),Eq(Cl(Old("boundary",V("r")),Sub(d,Parenthesized(Cost(p,V("r"))))),s)),Typed(Num(1),V("Int")),Typed(Num(0),V("Int")))),Data("T",Cl(p,d),s));
    private static Formula Join(params Formula[] a) => a.Length==1 ? a[0] : And(a[0],Join(a.Skip(1).ToArray()));

}
