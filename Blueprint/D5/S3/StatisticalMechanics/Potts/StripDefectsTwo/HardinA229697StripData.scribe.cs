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
    private static readonly string[][] CostTwo =
    [
        ["0", "0", "2", "0", "2", "2", "0", "2", "0", "2", "2", "4", "4", "4"],
        ["1", "0", "1", "1", "1", "2", "1", "0", "1", "2", "0", "2", "2", "2"],
        ["1", "1", "1", "1", "3", "1", "1", "3", "3", "2", "3", "2", "2", "2"],
        ["0", "0", "3", "0", "1", "1", "3", "2", "2", "1", "1", "1", "1", "0"],
        ["2", "1", "2", "0", "2", "2", "4", "3", "1", "2", "2", "2", "2", "1"],
        ["1", "1", "2", "3", "3", "1", "1", "3", "1", "1", "3", "2", "2", "2"],
        ["0", "0", "1", "3", "2", "1", "3", "2", "3", "1", "2", "4", "4", "4"],
        ["2", "1", "2", "1", "0", "2", "4", "3", "4", "2", "3", "2", "2", "2"],
        ["0", "2", "1", "2", "2", "3", "3", "2", "2", "1", "2", "1", "4", "1"],
        ["0", "1", "1", "0", "2", "1", "0", "2", "2", "0", "1", "4", "1", "1"],
        ["1", "1", "3", "1", "1", "3", "2", "1", "2", "0", "3", "3", "3", "2"],
        ["2", "4", "2", "1", "3", "2", "4", "0", "1", "2", "3", "2", "2", "2"],
        ["1", "2", "3", "2", "4", "3", "2", "4", "2", "0", "1", "0", "3", "3"],
        ["1", "2", "3", "1", "1", "3", "2", "4", "2", "1", "1", "3", "0", "2"],
    ];
    private static readonly string[][] CachedSector =
    [
        ["0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0", "0"],
        ["72", "96", "156", "96", "156", "156", "180", "180", "156", "96", "156", "180", "180", "156"],
        ["1746", "3456", "3054", "3474", "3138", "2988", "2292", "2292", "3114", "3618", "2934", "2622", "2442", "3222"],
        ["30924", "48744", "35172", "47100", "35832", "33678", "24318", "24870", "34944", "47652", "35532", "24396", "25524", "35856"],
        ["377202", "540492", "374580", "522492", "355488", "367932", "259230", "239592", "361146", "532020", "363588", "215148", "239208", "345504"],
        ["4054452", "5457192", "3686862", "5211834", "3253092", "3610926", "2525088", "2178282", "3451698", "5264016", "3399486", "1816680", "2112798", "3097872"],
        ["39973590", "51600240", "34305966", "48798738", "28515438", "33679518", "23386752", "19142430", "31561674", "49156692", "30342636", "14930280", "18094416", "26725488"],
        ["372843774", "466758576", "307038738", "438266286", "242741346", "302037042", "208500144", "163815486", "278838768", "440229924", "262043610", "120400578", "151445256", "224364660"],
        ["3342906258", "4087244490", "2668685268", "3816926418", "2021495418", "2629378596", "1806309216", "1372855800", "2399606766", "3824917806", "2209307268", "957022332", "1245811218", "1846778916"],
        ["29096291154", "34910163516", "22670154966", "32461946718", "16547751426", "22365238494", "15302283234", "11313015036", "20224996710", "32467056708", "18281788008", "7519187418", "10105568772", "14967598458"],
        ["247451918184", "292338981054", "189060677586", "270894647088", "133590929976", "186719668002", "127316871360", "91941158790", "167598672480", "270503213094", "149013874584", "58514728896", "81020012490", "119790127116"],
        ["2065614317316", "2408913672696", "1552907898288", "2225783676888", "1066175027496", "1535086607256", "1043644310982", "738566784198", "1369382616810", "2219557579812", "1199540257290", "451729913112", "643157973792", "948729250602"],
        ["16980131833650", "19585189731708", "12593521657458", "18052279830882", "8427076665426", "12458815447698", "8448662417508", "5874405151302", "11055958421922", "17980857343152", "9555129230112", "3463640377812", "5062208619672", "7447573600884"],
    ];
    private static readonly string[][] RemainingRows =
    [
        ["652281782796", "652281782796", "411865664976", "583315212132", "171449547156", "411865664976", "269125207020", "142740457956", "342899094312", "571766819868", "228867725556", "28709089200", "102482976492", "131192065692", "12384202863618", "13379383740726", "8470746755316", "12147692882022", "4741093574478", "8421564163788", "5619676998942", "3466522327950", "7230130786548", "12011423200110", "5695958327742", "1489036367916", "2759329808262", "3969626335902", "137797001681994", "157434547581540", "101023948880442", "144809868018546", "66058334920422", "100011877731162", "67669121286324", "46325456212050", "88353596824416", "144091237158360", "75431336812758", "26402024585970", "39549461286348", "58020609151800"],
        ["4547683011672", "4547683011672", "2871511262568", "4066850776032", "1195339513464", "2871511262568", "1876330385460", "995180877108", "2390679026928", "3986335813104", "1595656786176", "200158636356", "714507277824", "914665914180", "93083333842296", "100021695880896", "63314235148212", "90721644109164", "34826603235192", "62971336053900", "41961504253914", "25643642079258", "53951957881452", "89652226733676", "42077283692256", "10678203535194", "20297072591748", "29031912929826", "1106048892585906", "1253246019223554", "802830682440756", "1150664013227322", "514113418194570", "795266273232756", "537021181747404", "362600751299580", "699838011566478", "1143938316227022", "590856808948092", "200226128199840", "306979554317922", "449031221260848"],
        ["31706267561676", "31706267561676", "20020063875048", "28353924063468", "8333860188420", "20020063875048", "13081701836448", "6938362038600", "16667720376840", "27792576864900", "11124856488060", "1395498149820", "4981516690212", "6377014840032", "695972433537090", "744346421475606", "471100660560504", "674537552805186", "255163223681406", "468709981533576", "311945331471588", "189071393532732", "400857958211544", "666249514806978", "309851853837174", "76516601308794", "148894633496610", "211862182884588", "8794257672353454", "9892216370803896", "6328001981614014", "9068118287286906", "3976089930378918", "6271719447469302", "4227648899923026", "2819523296751444", "5500397675845926", "9008033685888456", "4596721332083100", "1511647900364142", "2369015138051208", "3454988842925514"],
        ["221054853576780", "221054853576780", "139579099926768", "197682446203524", "58103346276756", "139579099926768", "91205111988252", "48373987938516", "116206692553512", "193768755506748", "77562062953236", "9729358338240", "34730938903500", "44460297241740", "5179968252822366", "5517229798952658", "3491397300405132", "4995879535615698", "1865116188714114", "3474729580028292", "2310066483664662", "1389904444389870", "2967022365726348", "4932294285137778", "2275247367471690", "547892839804752", "1089570177378378", "1542999558810870", "69349075102647540", "77503932231300306", "49519675588443210", "70947747641475684", "30579809402453724", "49102568943638778", "33046756276934412", "21796120317830562", "42934562201725776", "70428257516407914", "35546240666611332", "11367038949008328", "18187940499564222", "26447169852734040"],
        ["1541185766835912", "1541185766835912", "973140008790600", "1378234259535888", "405094250745288", "973140008790600", "635878462660308", "337261546130292", "810188501490576", "1350948161465856", "540759659975280", "67832704614996", "242142743445264", "309975448060260", "38399077909780524", "40750452178107012", "25784397469456164", "36874071048721464", "13603999354891812", "25668190776902652", "17048273202993654", "10190291415759630", "21886928450202132", "36390310232378544", "16664518445132844", "3920437685330514", "7955375443002648", "11217217602612366", "542911141731655692", "603251993091531096", "385043727395666592", "551532971976560136", "234021853277252496", "381963419824024440", "256700030028357762", "167612398299530154", "333091756681103898", "547149893538619548", "273403680032385738", "85171608454963284", "138989625376493160", "201517452818736678"],
    ];
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect sheared square-lattice strip counts.",H("Two-defect HA strips"),Blocks(
        Describe.Lean(DescribeId.Create("valid"),DeclarationHandle.Create(Prefix+"Valid"),H("Valid"),StatementSource.FromAuthor(Disp(All("p",Row(),All("d",V("Nat"),Iff(Valid(V("p"),V("d")),Leq(V("d"),Num(2))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Residual budgets are at most two."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("cl"),DeclarationHandle.Create(Prefix+"cl"),H("cl"),StatementSource.FromAuthor(Disp(All("p",Row(),All("d",V("Nat"),Eq(Cl(V("p"),V("d")),If(Lt(Num(0),V("d")),Typed(Call("Fin.castAdd",Num(14),Old("cl",V("p"),Sub(V("d"),Num(1)))),Fin(States)),Typed(Call("Fin.natAdd",Num(28),Call("HardinA233177PairTransfer.cls",Parenthesized(Seq(App(V("p"),Typed(Num(0),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(1),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(2),Fin(Rows))),Comma,Sp,App(V("p"),Typed(Num(3),Fin(Rows))))))),Fin(States)))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("Positive budgets call the frozen one-defect classifier at d minus one. Zero budget selects the appended equality sector."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("t"),DeclarationHandle.Create(Prefix+"T"),H("T"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("T"),Call("Matrix",Fin(States),Fin(States),V("Int"))),Transfer()))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 42 by 42 integer matrix retains HardinA229589StripData.T in its leading 28 by 28 block. The added block records cost two and the inherited cost-one block; its diagonal is the frozen zero-temperature Q. The HardinA229697Strip.finite_certificate theorem pins every transition sum."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("initial"),DeclarationHandle.Create(Prefix+"initial"),H("initial"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("initial"),new Formula.TypeArrow(Fin(States),V("Int"))),Call("Fin.append",Old("initial"),Vector(Enumerable.Repeat(Num(0),Sector).ToArray()))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 42 integer initial weights append 14 zero entries to the frozen initial vector; HardinA229697Strip.finite_certificate pins the initial class counts."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("terminal"),DeclarationHandle.Create(Prefix+"terminal"),H("terminal"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("terminal"),new Formula.TypeArrow(Fin(States),V("Int"))),Call("Fin.append",Lambda("i",Fin(2*Sector),Typed(Num(0),V("Int"))),Lambda("i",Fin(Sector),Typed(Num(1),V("Int"))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 42 integer acceptance weights are zero on the leading 28 states and one on the final 14 states; HardinA229697Strip.finite_certificate pins acceptance at residual zero."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("w"),DeclarationHandle.Create(Prefix+"W"),H("W"),StatementSource.FromAuthor(Disp(Eq(Typed(Data("W"),new Formula.TypeArrow(Fin(Last+1),new Formula.TypeArrow(Fin(States),V("Int")))),Call("Fin.append",Lambda("i",Fin(CachedSector.Length),Call("Fin.append",Old("W",V("i")),App(Typed(Matrix(CachedSector),MatrixType(CachedSector.Length,Sector)),V("i")))),Typed(Matrix(RemainingRows),MatrixType(RemainingRows.Length,States)))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),Blocks(Paragraph(Text("The 18 by 42 integer table appends the new sector to the first 13 cached rows of HardinA229589StripData.W, then tabulates the remaining rows. HardinA229697StripForward.forward_certificate pins its initial row, every successor row, and its polynomial relation."))),DescribeRole.Definition))));

    private const int Sector=14;
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
                Typed(Num(0),MatrixType(Sector,2*Sector)),Call("HardinA233259PairTransferCore.Q")));
    }
    private static Formula Matrix(string[][] rows) => Seq(
        new[] { Begin,Grp(F.Id("bmatrix")) }
            .Concat(rows.SelectMany((row,i) =>
                (i==0 ? Array.Empty<Formula>() : new[] { new Formula.LatexMacro(FormulaLatexMacro.RowBreak) })
                    .Concat(row.SelectMany((entry,j) =>
                        j==0 ? new[] { Num(entry) }
                            : new[] { Amp,Num(entry) }))))
            .Concat(new[] { End,Grp(F.Id("bmatrix")) }).ToArray());
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
