using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a;
internal sealed class HardinA229537StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-row exact-defect HDA strips.",H("HardinA229537StripCertificate"),Blocks(
            Paragraph(Text("Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer.")),
            Node("zero_counts",CountSector(0),true),
            Node("one_counts",CountSector(1),true),
            Node("cost_relabel",Relabel(),true),
            Node("Z",ZeroTable(),false),
            Node("zero_powers",All("i",Fin(22),Eq(Call("Matrix.mulVec",Call("HPow.hPow",Old("Q"),Val(V("i"))),IntVec(N(1),14)),Cert("Z",V("i")))),true),
            Node("W",Table(),false),
            Node("powers",All("i",Fin(22),Eq(Power(Val(V("i"))),Cert("W",V("i")))),true),
            Node("finite_certificate",Certificate(),true))));
    private static DocumentBlock Node(string name,Formula formula,bool theorem) => Describe.Lean(
        DescribeId.Create(name.Replace("_","-")),DeclarationHandle.Create(Prefix+name),H(name),
        StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229537")),
        Blocks(Paragraph(Text("Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer."))),theorem?DescribeRole.Theorem:DescribeRole.Definition);
    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Row() => Arrow(Fin(4),Fin(3));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b) => Seq(Parenthesized(a),Times,Parenthesized(b));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Fn(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Mapsto,Sp,Parenthesized(b)));
    private static Formula Sum(string n,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula y,Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n,params Formula[] a) => Call("HardinA229537StripData."+n,a);
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229537Strip."+n,a);
    private static Formula Old(string n,params Formula[] a) => Call("HardinA233177PairTransfer."+n,a);
    private static Formula IntVec(Formula x,int n) => Typed(x,Arrow(Fin(n),Q("Int")));
    private static Formula Power(Formula n) => Call("Matrix.mulVec",Call("HPow.hPow",Data("T"),n),Data("terminal"));
    private static Formula[] Coeffs() => new long[]{-16,-16,196,124,-741,-238,787,250,-288,-102,23,6}.Select(N).ToArray();
    private static Formula Vector(params Formula[] a) => Matrix(a);
    private static Formula Matrix(params Formula[][] rows) {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++){if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());}
    private static Formula Cert(string n,params Formula[] a) => Call("HardinA229537StripCertificate."+n,a);
    private static Formula Col() => Old("Col");
    private static Formula Tuple(Formula p) => Pair(App(p,N(0)),Pair(App(p,N(1)),Pair(App(p,N(2)),App(p,N(3)))));
    private static Formula Cost(Formula p,Formula r) => Call("DefectTransfer.bondDefects",Data("between"),p,r);
    private static Formula CountSector(int d) {
        var p=V("p");var r=V("r");var j=V("j");var c=Old("cls",Tuple(p));
        var right=d==0?Old("Q",c,j):Data("T",Call("Fin.castAdd",N(14),c),Call("Fin.natAdd",N(14),j));
        return All("p",Row(),All("j",Fin(14),Eq(Sum("r",Row(),If(And(Eq(Cost(p,r),N(d)),Eq(Old("cls",Tuple(r)),j)),Typed(N(1),Q("Int")),Typed(N(0),Q("Int")))),right)));
    }
    private static Formula Relabel() {
        var e=V("e");var p=V("p");var r=V("r");
        Formula col(Formula c)=>Old("column",c);
        Formula rel(Formula c)=>App(Typed(Old("relabel",e),Arrow(Col(),Col())),c);
        return All("e",Call("Equiv.Perm",Fin(3)),All("p",Col(),All("r",Col(),Eq(Cost(col(rel(p)),col(rel(r))),Cost(col(p),col(r))))));
    }
    private static Formula ZeroTable() => Eq(Cert("Z"),Call("Fin.append",Old("W"),Typed(Matrix(new Formula[]{N(2340880),N(783812),N(557050),N(719483),N(0),N(557050),N(417502),N(0),N(417502),N(783812),N(127826),N(0),N(0),N(0)},new Formula[]{N(13154182),N(4401225),N(3124692),N(4036330),N(0),N(3124692),N(2340880),N(0),N(2340880),N(4401225),N(719483),N(0),N(0),N(0)},new Formula[]{N(73848212),N(24716429),N(17555407),N(22676115),N(0),N(17555407),N(13154182),N(0),N(13154182),N(24716429),N(4036330),N(0),N(0),N(0)},new Formula[]{N(414752726),N(138796163),N(98564641),N(127317400),N(0),N(98564641),N(73848212),N(0),N(73848212),N(138796163),N(22676115),N(0),N(0),N(0)},new Formula[]{N(2328976316),N(779430930),N(553548889),N(715021167),N(0),N(553548889),N(414752726),N(0),N(414752726),N(779430930),N(127317400),N(0),N(0),N(0)},new Formula[]{N(13078925146),N(4376977302),N(3108407246),N(4015155576),N(0),N(3108407246),N(2328976316),N(0),N(2328976316),N(4376977302),N(715021167),N(0),N(0),N(0)},new Formula[]{N(73445604900),N(24579465270),N(17455902448),N(22547900917),N(0),N(17455902448),N(13078925146),N(0),N(13078925146),N(24579465270),N(4015155576),N(0),N(0),N(0)},new Formula[]{N(412444183090),N(138028873535),N(98025070170),N(126619691016),N(0),N(98025070170),N(73445604900),N(0),N(73445604900),N(138028873535),N(22547900917),N(0),N(0),N(0)},new Formula[]{N(2316125942632),N(775117817811),N(550473056625),N(711049831077),N(0),N(550473056625),N(412444183090),N(0),N(412444183090),N(775117817811),N(126619691016),N(0),N(0),N(0)},new Formula[]{N(13006491777522),N(4352766648145),N(3091243760443),N(3992981269270),N(0),N(3091243760443),N(2316125942632),N(0),N(2316125942632),N(4352766648145),N(711049831077),N(0),N(0),N(0)},new Formula[]{N(73039491498464),N(24443483455380),N(17359258425667),N(22423074904889),N(0),N(17359258425667),N(13006491777522),N(0),N(13006491777522),N(24443483455380),N(3992981269270),N(0),N(0),N(0)},new Formula[]{N(410162067440982),N(137265308284400),N(97482974953844),N(125919439678494),N(0),N(97482974953844),N(73039491498464),N(0),N(73039491498464),N(137265308284400),N(22423074904889),N(0),N(0),N(0)},new Formula[]{N(2303314113185784),N(770829790357720),N(547427375725382),N(707115758914671),N(0),N(547427375725382),N(410162067440982),N(0),N(410162067440982),N(770829790357720),N(125919439678494),N(0),N(0),N(0)},new Formula[]{N(12934536678297246),N(4328687038183557),N(3074143903543504),N(3970893133579718),N(0),N(3074143903543504),N(2303314113185784),N(0),N(2303314113185784),N(4328687038183557),N(707115758914671),N(0),N(0),N(0)}),Arrow(Fin(14),Arrow(Fin(14),Q("Int"))))));
    private static Formula Table() => All("i",Fin(22),Eq(Cert("W",V("i")),Call("Fin.append",App(Typed(Matrix(new Formula[]{N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0),N(0)},new Formula[]{N(0),N(12),N(8),N(8),N(6),N(8),N(6),N(3),N(6),N(12),N(6),N(0),N(3),N(6)},new Formula[]{N(120),N(49),N(31),N(42),N(9),N(31),N(20),N(8),N(20),N(49),N(20),N(0),N(8),N(9)},new Formula[]{N(724),N(428),N(322),N(328),N(55),N(322),N(264),N(51),N(264),N(428),N(134),N(0),N(51),N(55)},new Formula[]{N(6160),N(2704),N(1903),N(2150),N(288),N(1903),N(1468),N(263),N(1468),N(2704),N(794),N(0),N(263),N(288)},new Formula[]{N(40920),N(18296),N(13321),N(14982),N(1652),N(13321),N(10470),N(1528),N(10470),N(18296),N(4878),N(0),N(1528),N(1652)},new Formula[]{N(280152),N(117021),N(83683),N(96664),N(9184),N(83683),N(64826),N(8447),N(64826),N(117021),N(30046),N(0),N(8447),N(9184)},new Formula[]{N(1815752),N(744816),N(535878),N(625464),N(51775),N(535878),N(415062),N(47749),N(415062),N(744816),N(181846),N(0),N(47749),N(51775)},new Formula[]{N(11665456),N(4657599),N(3336391),N(3940754),N(290259),N(3336391),N(2571816),N(267374),N(2571816),N(4657599),N(1102432),N(0),N(267374),N(290259)},new Formula[]{N(73475644),N(28863570),N(20687092),N(24636152),N(1631121),N(20687092),N(15914804),N(1503295),N(15914804),N(28863570),N(6622478),N(0),N(1503295),N(1631121)},new Formula[]{N(458085456),N(177198520),N(126828621),N(152147306),N(9157038),N(126828621),N(97329928),N(8437555),N(97329928),N(177198520),N(39687986),N(0),N(8437555),N(9157038)},new Formula[]{N(2825893800),N(1080173062),N(772848457),N(932633526),N(51428874),N(772848457),N(592061986),N(47392544),N(592061986),N(1080173062),N(236690978),N(0),N(47392544),N(51428874)},new Formula[]{N(17297388672),N(6543135579),N(4678478409),N(5674694984),N(288789678),N(4678478409),N(3578207734),N(266113563),N(3578207734),N(6543135579),N(1407355134),N(0),N(266113563),N(288789678)},new Formula[]{N(105143454200),N(39425416516),N(28178327908),N(34328155076),N(1621769497),N(28178327908),N(21522210170),N(1494452097),N(21522210170),N(39425416516),N(8340654622),N(0),N(1494452097),N(1621769497)},new Formula[]{N(635447036928),N(236454026529),N(168927769187),N(206582067498),N(9107154045),N(168927769187),N(128868177900),N(8392132878),N(128868177900),N(236454026529),N(49298924172),N(0),N(8392132878),N(9107154045)},new Formula[]{N(3821058103316),N(1412391957008),N(1008692705678),N(1237661620888),N(51142521763),N(1008692705678),N(768676702904),N(47127366187),N(768676702904),N(1412391957008),N(290652802934),N(0),N(47127366187),N(51142521763)},new Formula[]{N(22876484910768),N(8406271468352),N(6001616749467),N(7385784342638),N(287196465468),N(6001616749467),N(4569223737796),N(264648564551),N(4569223737796),N(8406271468352),N(1709769508298),N(0),N(264648564551),N(287196465468)},new Formula[]{N(136432986329272),N(49872853461284),N(35596496016265),N(43921843131174),N(1612787339904),N(35596496016265),N(27077902295262),N(1486167648888),N(27077902295262),N(49872853461284),N(10036966091510),N(0),N(1486167648888),N(1612787339904)},new Formula[]{N(810898666012136),N(295040520004921),N(210530143593343),N(260384109402776),N(9056797748492),N(210530143593343),N(160026540442738),N(8345747917415),N(160026540442738),N(295040520004921),N(58809863948350),N(0),N(8345747917415),N(9056797748492)},new Formula[]{N(4804954366993832),N(1740921354610008),N(1241973709508354),N(1539354236631440),N(50859539629539),N(1241973709508354),N(943391116684990),N(46866558360269),N(943391116684990),N(1740921354610008),N(343989593164870),N(0),N(46866558360269),N(50859539629539)},new Formula[]{N(28393761930463952),N(10248546583403267),N(7309793785660639),N(9077591498643394),N(285607822867783),N(7309793785660639),N(5548981550039120),N(263184747962894),N(5548981550039120),N(10248546583403267),N(2008850803107928),N(0),N(263184747962894),N(285607822867783)},new Formula[]{N(167371994534626796),N(60203605630137598),N(42932182179508552),N(53408792169658520),N(1603864988950885),N(42932182179508552),N(32571935843345596),N(1477945549272391),N(32571935843345596),N(60203605630137598),N(11714105830809598),N(0),N(1477945549272391),N(1603864988950885)}),Arrow(Fin(22),Arrow(Fin(14),Q("Int")))),V("i")),Cert("Z",V("i")))));

    private static Formula Certificate() {
        var p=V("p");var r=V("r");var d=V("d");var s=V("s");var cost=Call("DefectTransfer.bondDefects",Data("between"),p,r);
        var trans=All("p",Row(),All("d",Fin(2),All("s",Fin(28),Eq(Sum("r",Row(),If(And(Le(cost,Val(d)),Eq(Data("cl",r,Sub(Val(d),cost)),s)),Typed(N(1),Q("Int")),Typed(N(0),Q("Int")))),Data("T",Data("cl",p,Val(d)),s)))));
        var poly=Eq(Power(N(14)),Sum("k",Fin(12),Call("HSMul.hSMul",App(IntVec(Vector(Coeffs()),12),V("k")),Power(Add(N(2),Val(V("k")))))));
        return And(trans,poly);
    }

}
