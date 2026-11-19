using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide;
internal sealed class HardinA229692StripInheritedDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited.";
    private const string Note="D5/L/SpinModels/hardin2013a229692";
    private const string DataName="HardinA229692StripData",OldName="HardinA229584StripData";
    private const int Rows=6,States=68,Last=11,Start=2;
    private static readonly int[] Coefficients=[531441,-1771470,2460375,-1842183,803115,-205200,29368,-2145,75];
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect six-column sheared square-lattice counts.",H("Two-defect HA strips"),Blocks(
        Describe.Lean(DescribeId.Create("step"),DeclarationHandle.Create(Prefix+"step"),H("step"),StatementSource.FromAuthor(Disp(All("i",Fin(11),Imp(All("j",Fin(36),Imp(Seq(Neg,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(7))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(11))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(16))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(20))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(26))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(29))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(30))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(31))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(34))),Sp,Lor,Sp,Parenthesized(Eq(Val(V("j")),Num(35)))))))))))))))))))))),Eq(App(Call("HardinA229692StripData.W",Call("Fin.succ",V("i"))),Call("Fin.natAdd",Num(32),V("j"))),App(Call("Matrix.vecMul",Call("HardinA229692StripData.W",Call("Fin.castSucc",V("i"))),Call("HardinA229692StripData.T")),Call("Fin.natAdd",Num(32),V("j")))))),Eq(Call("HardinA229692StripData.W",Call("Fin.succ",V("i"))),Call("Matrix.vecMul",Call("HardinA229692StripData.W",Call("Fin.castSucc",V("i"))),Call("HardinA229692StripData.T"))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The lower-left block is zero. HardinA229584Strip.powers_table supplies the leading prefix; its forward evolution supplies the remaining leading coordinates. Ten identical matrix columns copy those steps; only the other twenty-six coordinates require a numerical premise."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("polynomial"),DeclarationHandle.Create(Prefix+"polynomial"),H("polynomial"),StatementSource.FromAuthor(Disp(Imp(All("j",Fin(36),Imp(Seq(Neg,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(7))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(11))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(16))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(20))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(26))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(29))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(30))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(31))),Sp,Lor,Sp,Parenthesized(Seq(Parenthesized(Eq(Val(V("j")),Num(34))),Sp,Lor,Sp,Parenthesized(Eq(Val(V("j")),Num(35)))))))))))))))))))))),Eq(Call("HardinA229692StripData.W",Typed(Num(11),Fin(12)),Call("Fin.natAdd",Num(32),V("j"))),App(Sum("k",Fin(9),Call("HSMul.hSMul",Typed(App(Vector(Coefficients.Select(x => Num(x)).ToArray()),V("k")),V("Int")),Data("W",Typed(Call("Fin.mk",Add(Num(2),Val(V("k")))),Fin(12))))),Call("Fin.natAdd",Num(32),V("j")))))),Clauses()[6]))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Advance HardinA229584Strip.polynomial_relation and multiply its monic polynomial by X cubed minus twenty-five X squared plus ninety X minus eighty-one. Linearity supplies the inherited relation; only twenty-six new coordinates require a numerical premise."))),DescribeRole.Theorem))));

    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus, Num(-n))) : new Formula.Number(n);
    private static Formula V(string n) => new Formula.Symbol(FormulaIdentifier.Create(n));
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i) => i == 0 ? new[] { Seq(Operatorname, Grp(V(p))) } : new[] { Dot, Seq(Operatorname, Grp(V(p))) }).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length == 0 ? Q(n) : new Formula.Apply(Q(n), [..a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
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
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a),Sp,Implies,Sp,Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n, params Formula[] a) => Call(DataName+"."+n,a);
    private static Formula Old(string n, params Formula[] a) => Call(OldName+"."+n,a);
    private static Formula Boundary() => new Formula.TypeArrow(Fin(5),Fin(3));
    private static Formula Cost(Formula p, Formula r) => Add(Old("cross",p,r),Call("DefectTransfer.bondDefects",Old("horizontal"),r,r));
    private static Formula Valid(Formula p, Formula d) => Data("Valid",p,d);
    private static Formula Cl(Formula p, Formula d) => Data("cl",p,d);
    private static Formula Transition(Formula p, Formula d, Formula s) => Eq(Sum("r",Row(),If(And(Leq(Cost(p,V("r")),d),Eq(Cl(Old("boundary",V("r")),Sub(d,Parenthesized(Cost(p,V("r"))))),s)),Typed(Num(1),V("Int")),Typed(Num(0),V("Int")))),Data("T",Cl(p,d),s));
    private static Formula[] Clauses()
    {
        var p=V("p");var d=V("d");var r=V("r");var s=V("s");var dv=Val(d);
        var internalCost=Call("DefectTransfer.bondDefects",Old("horizontal"),r,r);
        return [
            All("p",Boundary(),All("d",Fin(3),Imp(Valid(p,dv),Eq(Data("terminal",Cl(p,dv)),If(Eq(dv,Num(0)),Typed(Num(1),V("Int")),Typed(Num(0),V("Int"))))))),
            All("p",Boundary(),All("d",Fin(3),Imp(Valid(p,dv),All("r",Row(),Imp(Leq(Cost(p,r),dv),Valid(Old("boundary",r),Sub(dv,Parenthesized(Cost(p,r))))))))),
            All("p",Boundary(),All("d",Fin(3),Imp(Valid(p,dv),All("s",Fin(States),Transition(p,dv,s))))),
            All("r",Row(),Imp(Leq(internalCost,Num(2)),Valid(Old("boundary",r),Sub(Num(2),internalCost)))),
            All("s",Fin(States),Eq(Sum("r",Row(),If(And(Leq(internalCost,Num(2)),Eq(Cl(Old("boundary",r),Sub(Num(2),internalCost)),s)),Typed(Num(1),V("Int")),Typed(Num(0),V("Int")))),Data("initial",s))),
            And(Eq(Data("W",Typed(Num(0),Fin(Last+1))),Data("initial")),All("i",Fin(Last),Eq(Data("W",Call("Fin.succ",V("i"))),Call("Matrix.vecMul",Data("W",Call("Fin.castSucc",V("i"))),Data("T"))))),
            Eq(Data("W",Typed(Num(Last),Fin(Last+1))),Sum("j",Fin(Coefficients.Length),Call("HSMul.hSMul",Typed(App(Vector(Coefficients.Select(x => Num(x)).ToArray()),V("j")),V("Int")),Data("W",Typed(Call("Fin.mk",Add(Num(Start),Val(V("j")))),Fin(Last+1))))))
        ];
    }
    private static Formula Join(params Formula[] a) => a.Length==1 ? a[0] : And(a[0],Join(a.Skip(1).ToArray()));
    private static Formula Vector(params Formula[] a)
    {
        if (a.Length <= 9) return Matrix(a);
        var groups = new List<Formula>();
        for (var i = 0; i < a.Length; i += 9)
        {
            var row = new List<Formula>();
            for (var j = i; j < a.Length && j < i + 9; j++) row.Add(a[j]);
            groups.Add(Matrix(row.ToArray()));
        }
        return Matrix(groups.ToArray());
    }

    private static Formula Matrix(params Formula[][] rows)
    {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++) {if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());
    }
}
