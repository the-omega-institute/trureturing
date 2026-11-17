using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo;
internal sealed class HardinA229696StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.";
    private const string Note="D5/L/SpinModels/hardin2013a229696";
    private const string DataName="HardinA229696StripData";
    private const string OldName="HardinA229588Strip";
    private const int Rows=3;
    private const int States=15;
    private const int Last=10;
    private static readonly string[][] CostTwo =
    [
        ["0", "0", "2", "2", "4"],
        ["1", "0", "2", "2", "1"],
        ["1", "3", "2", "2", "4"],
        ["0", "1", "3", "0", "2"],
        ["2", "2", "4", "1", "3"],
    ];
    private static readonly string[][] CachedSector =
    [
        ["0", "0", "0", "0", "0"],
        ["24", "36", "72", "36", "72"],
        ["366", "816", "834", "894", "846"],
        ["4224", "7332", "5646", "7218", "6042"],
        ["33834", "52350", "38058", "51972", "38736"],
        ["236910", "341058", "239400", "335202", "229728"],
        ["1527054", "2092122", "1436118", "2038908", "1308276"],
    ];
    private static readonly string[][] RemainingRows =
    [
        ["218736", "218736", "140076", "201492", "61416", "1768404", "2109972", "1353222", "2003550", "1009140", "9318006", "12306282", "8322696", "11917530", "7244400"],
        ["997776", "997776", "638964", "919116", "280152", "9266460", "10824540", "6941118", "10244478", "4940100", "54676854", "70181538", "46970190", "67629276", "39274884"],
        ["4551408", "4551408", "2914668", "4192596", "1277928", "47742324", "54849588", "35167038", "51772134", "24071172", "311516334", "390787938", "259551624", "375074658", "209417616"],
        ["20761488", "20761488", "13295412", "19124748", "5829336", "242743932", "275164092", "176403462", "259158006", "116811444", "1734312126", "2134897578", "1409796150", "2042284812", "1101745716"],
    ];
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect sheared square-lattice strip counts.",H("Two-defect HA strips"),Blocks(
        Describe.Lean(DescribeId.Create("valid"),DeclarationHandle.Create(Prefix+"Valid"),H("Valid"),StatementSource.FromAuthor(Disp(All("p",Row(),All("d",V("Nat"),Iff(Valid(V("p"),V("d")),Leq(V("d"),Num(2))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Residual budgets are at most two."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("cl"),DeclarationHandle.Create(Prefix+"cl"),H("cl"),StatementSource.FromAuthor(Disp(All("p",Row(),All("d",V("Nat"),Eq(Cl(V("p"),V("d")),If(Lt(Num(0),V("d")),Typed(Call("Fin.castAdd",Num(5),Old("cl",V("p"),Sub(V("d"),Num(1)))),Fin(States)),Typed(Call("Fin.natAdd",Num(10),Call("HardinA233258PairTransfer.cls",Parenthesized(Seq(App(V("p"),Typed(Num(0),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(1),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(2),Fin(Rows))))))),Fin(States)))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Positive budgets call the frozen one-defect classifier at d minus one. Zero budget selects the appended equality sector."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("t"),DeclarationHandle.Create(Prefix+"T"),H("T"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("T"),Call("Matrix",Fin(States),Fin(States),V("Int"))),Transfer()))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 15 by 15 integer matrix retains HardinA229588Strip.T in its leading 10 by 10 block. The added block records cost two and the inherited cost-one block; its diagonal is the frozen zero-temperature Q. The HardinA229696Strip.finite_certificate theorem pins every transition sum."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("initial"),DeclarationHandle.Create(Prefix+"initial"),H("initial"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("initial"),new Formula.TypeArrow(Fin(States),V("Int"))),Call("Fin.append",Old("initial"),Vector(Enumerable.Repeat(Num(0),Sector).ToArray()))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 15 integer initial weights append 5 zero entries to the frozen initial vector; HardinA229696Strip.finite_certificate pins the initial class counts."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("terminal"),DeclarationHandle.Create(Prefix+"terminal"),H("terminal"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("terminal"),new Formula.TypeArrow(Fin(States),V("Int"))),Call("Fin.append",Lambda("i",Fin(2*Sector),Typed(Num(0),V("Int"))),Lambda("i",Fin(Sector),Typed(Num(1),V("Int"))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 15 integer acceptance weights are zero on the leading 10 states and one on the final 5 states; HardinA229696Strip.finite_certificate pins acceptance at residual zero."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("w"),DeclarationHandle.Create(Prefix+"W"),H("W"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("W"),new Formula.TypeArrow(Fin(Last+1),new Formula.TypeArrow(Fin(States),V("Int")))),Call("Fin.append",Lambda("i",Fin(CachedSector.Length),Call("Fin.append",Old("W",V("i")),App(Typed(Matrix(CachedSector),MatrixType(CachedSector.Length,Sector)),V("i")))),Typed(Matrix(RemainingRows),MatrixType(RemainingRows.Length,States)))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 11 by 15 integer table appends the new sector to the first 7 cached rows of HardinA229588Strip.W, then tabulates the remaining rows. HardinA229696StripForward.forward_certificate pins its initial row, every successor row, and its polynomial relation."))),DescribeRole.Definition))));

    private const int Sector=5;
    private static Formula MatrixType(int m, int n) => Call("Matrix",Fin(m),Fin(n),V("Int"));
    private static Formula Lambda(string n, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower,Sp,V(n),Colon,Sp,t,Comma,Sp,Parenthesized(b)));
    private static Formula Transfer()
    {
        var equivalence=Typed(Call("finSumFinEquiv"),Call("Equiv",Call("Sum",Fin(2*Sector),Fin(Sector)),Fin(States)));
        return Call("Matrix.reindex",equivalence,equivalence,
            Call("Matrix.fromBlocks",Old("T"),
                Call("Fin.append",Typed(Matrix(CostTwo),MatrixType(Sector,Sector)),
                    Call("Matrix.submatrix",Old("T"),
                        Lambda("i",Fin(Sector),Call("Fin.castAdd",Num(Sector),V("i"))),
                        Lambda("j",Fin(Sector),Call("Fin.natAdd",Num(Sector),V("j"))))),
                Typed(Num(0),MatrixType(Sector,2*Sector)),Call("HardinA233258PairTransfer.Q")));
    }
    private static Formula Matrix(string[][] rows) => Seq(
        new[] { Begin,Grp(V("bmatrix")) }
            .Concat(rows.SelectMany((row,i) =>
                (i==0 ? Array.Empty<Formula>() : new[] { new Formula.LatexMacro(FormulaLatexMacro.RowBreak) })
                    .Concat(row.SelectMany((entry,j) =>
                        j==0 ? new[] { Num(entry) }
                            : new[] { Amp,Num(entry) }))))
            .Concat(new[] { End,Grp(V("bmatrix")) }).ToArray());
    private static Formula Vector(params Formula[] a) => Seq(
        new Formula[] { Bang,OpenBracket }.Concat(a.SelectMany((f,i) =>
            i==0 ? new[] { f } : new[] { Comma,Sp,f })).Append(CloseBracket).ToArray());
    private static Formula Num(string n) => D(n.Select(c => (byte)(c-'0')).ToArray());

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
