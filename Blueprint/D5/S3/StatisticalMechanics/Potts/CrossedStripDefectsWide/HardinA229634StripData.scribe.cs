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
                H("Class map"), StatementSource.FromAuthor(Disp(FullCl())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The function retains HardinA229531StripData.cl at positive residual budget, subtracts one from the budget and embeds Fin 20 into Fin 33. At zero residual it appends thirteen classes: six proper classes followed by seven classes of identical zero-cost successor counts. The equality code sums powers of two for the ten equal-position predicates. Membership in each finite code set selects a class. Nat.mod denotes the nonnegative remainder modulo six. HardinA229634StripClasses.transition_counts pins every class against actual rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("old-tail"), DeclarationHandle.Create(Prefix + "oldTail"),
                H("One-defect destination image"), StatementSource.FromAuthor(Disp(All("i", Fin(20), Eq(Typed(Call("HardinA229634StripData.oldTail", V("i")), new Formula.TypeArrow(Fin(13), Call("Int"))), Vec(Call("HardinA229531StripData.T" , V("i"), Num("6")), Call("HardinA229531StripData.T" , V("i"), Num("7")), Call("HardinA229531StripData.T" , V("i"), Num("8")), Call("HardinA229531StripData.T" , V("i"), Num("9")), Call("HardinA229531StripData.T" , V("i"), Num("10")), Call("HardinA229531StripData.T" , V("i"), Num("11")), Add(Call("HardinA229531StripData.T" , V("i"), Num("16")), Call("HardinA229531StripData.T" , V("i"), Num("18"))), Num("0"), Call("HardinA229531StripData.T" , V("i"), Num("13")), Num("0"), Call("HardinA229531StripData.T" , V("i"), Num("12")), Add(Add(Call("HardinA229531StripData.T" , V("i"), Num("14")), Call("HardinA229531StripData.T" , V("i"), Num("17"))), Call("HardinA229531StripData.T" , V("i"), Num("19"))), Call("HardinA229531StripData.T" , V("i"), Num("15"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The thirteen destination columns are the finite image of the frozen one-defect transfer. Merged destination classes are added; empty fibres give zero. HardinA229634StripClasses.transition_counts pins this image on actual rows."))), DescribeRole.Definition),
            TableDefinition("t", "T", "Block extension", FullT, "The 33 by 33 integer matrix is reindexed from a 20 plus 13 block matrix. Its upper left block is exactly HardinA229531StripData.T and its lower left block is zero. The oldTail submatrices and indexed rows reuse the frozen one-defect transfer on its entire image; only the remaining sectors have literal rows. All appended entries are pinned by HardinA229634StripClasses.transition_counts."),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("Initial distribution"), StatementSource.FromAuthor(Disp(FullInitial())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Fin.append retains HardinA229531StripData.initial and appends thirteen weights counting initial rows with two horizontal defects. The literal initial-row sum is checked in HardinA229634Strip.finite_certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
                H("Terminal indicator"), StatementSource.FromAuthor(Disp(FullTerminal())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first twenty entries are zero and the appended thirteen entries are one. The finite certificate identifies this with zero residual budget for every valid row."))), DescribeRole.Definition),
            TableDefinition("w", "W", "Forward vectors", FullW, "The 21 by 33 integer table keeps all fourteen available forward rows from HardinA229531StripData.W in the inherited block. The remaining entries are explicit integers. HardinA229634Strip.finite_certificate pins row zero to initial, all twenty matrix steps, and the order-eighteen relation at row twenty."))));
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
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula EqualSign { get; } = F.Eq;
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Vec(params Formula[] cells) => Mat(cells);
    private static Formula Mat(params Formula[][] rows) => Seq(Begin, Grp(F.Id("pmatrix")),
        Seq(rows.SelectMany((row, i) => (i == 0 ? Array.Empty<Formula>() : new[] { RowBreak })
            .Concat(row.SelectMany((cell, j) => j == 0 ? new[] { cell } : new[] { Amp, cell }))).ToArray()),
        End, Grp(F.Id("pmatrix")));
    private static Formula Set(params Formula[] cells) => Seq(OpenBrace,
        Seq(cells.SelectMany((cell, i) => i == 0 ? new[] { cell } : new[] { Comma, Sp, cell }).ToArray()), CloseBrace);
    private static Formula Cond(Formula test, Formula yes, Formula no) => Parenthesized(Seq(
        Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp,
        Call("else"), Sp, Parenthesized(no)));
    private static Formula Fun(string n, Formula type, Formula value) => Parenthesized(Seq(
        Lambda, Sp, Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(value)));

    private static DocumentBlock TableDefinition(string id, string name, string title,
        Func<List<DocumentBlock>, Formula> full, string prose)
    {
        var tables = new List<DocumentBlock>();
        var statement = full(tables);
        return Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks([Paragraph(Text(prose)), Paragraph(Text("Each displayed B subscript names only a row block of this presentation, with zero-based row and column indices. The Fin.append expressions concatenate these blocks in order along their first index. Every block is displayed in full below.")), .. tables]),
            DescribeRole.Definition);
    }
    private static Formula Table(List<DocumentBlock> tables, params Formula[][] rows)
    {
        var blocks = new List<Formula>();
        for (var offset = 0; offset < rows.Length; offset += 3)
        {
            var count = rows.Length - offset < 3 ? rows.Length - offset : 3;
            var chunk = new Formula[count][];
            for (var row = 0; row < count; row++)
                chunk[row] = rows[offset + row];
            var symbol = Seq(V("B"), Underscore, Grp(Num(tables.Count.ToString(System.Globalization.CultureInfo.InvariantCulture))));
            tables.Add(new DocumentBlock.DisplayFormula(Disp(Eq(
                Typed(symbol, Call("Matrix", Fin(chunk.Length), Fin(chunk[0].Length), Call("Int"))), Mat(chunk)))));
            blocks.Add(symbol);
        }
        var result = blocks[blocks.Count - 1];
        for (var i = blocks.Count - 2; i >= 0; i--)
            result = Call("Fin.append", blocks[i], result);
        return result;
    }

    private static Formula FullCl() =>
        All("p", RowType(), All("d", Call("Nat"), Eq(Typed(Call("HardinA229634StripData.cl", V("p"), V("d")), Fin(33)), Cond(Seq(Num("0"), Lt, V("d")), Call("Fin.castAdd", Num("13"), Call("HardinA229531StripData.cl", V("p"), Sub(V("d"), Num("1")))), Cond(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229531StripData.horizontal"), V("p"), V("p")), Num("0")), Add(Num("20"), Call("Nat.mod", Call("Fin.val", Call("HardinA229531StripData.cl", V("p"), Num("0"))), Num("6"))), Seq(Call("let"), Sp, Typed(V("code"), Call("Nat")), Sp, EqualSign, Sp, Add(Add(Add(Add(Add(Add(Add(Add(Add(Cond(Eq(Call("p", Num("0")), Call("p", Num("1"))), Num("1"), Num("0")), Cond(Eq(Call("p", Num("0")), Call("p", Num("2"))), Num("2"), Num("0"))), Cond(Eq(Call("p", Num("0")), Call("p", Num("3"))), Num("4"), Num("0"))), Cond(Eq(Call("p", Num("0")), Call("p", Num("4"))), Num("8"), Num("0"))), Cond(Eq(Call("p", Num("1")), Call("p", Num("2"))), Num("16"), Num("0"))), Cond(Eq(Call("p", Num("1")), Call("p", Num("3"))), Num("32"), Num("0"))), Cond(Eq(Call("p", Num("1")), Call("p", Num("4"))), Num("64"), Num("0"))), Cond(Eq(Call("p", Num("2")), Call("p", Num("3"))), Num("128"), Num("0"))), Cond(Eq(Call("p", Num("2")), Call("p", Num("4"))), Num("256"), Num("0"))), Cond(Eq(Call("p", Num("3")), Call("p", Num("4"))), Num("512"), Num("0"))), Sp, Call("in"), Sp, Cond(Seq(V("code"), Sp, InMacro, Sp, Set(Num("201"), Num("129"), Num("198"), Num("540"), Num("340"), Num("20"), Num("176"), Num("528"), Num("192"))), Num("26"), Cond(Seq(V("code"), Sp, InMacro, Sp, Set(Num("513"))), Num("27"), Cond(Seq(V("code"), Sp, InMacro, Sp, Set(Num("37"), Num("608"))), Num("28"), Cond(Seq(V("code"), Sp, InMacro, Sp, Set(Num("621"), Num("184"))), Num("29"), Cond(Seq(V("code"), Sp, InMacro, Sp, Set(Num("293"), Num("610"))), Num("30"), Cond(Seq(V("code"), Sp, InMacro, Sp, Set(Num("347"), Num("19"), Num("73"), Num("910"), Num("134"), Num("24"), Num("336"), Num("524"), Num("136"), Num("896"))), Num("31"), Num("32")))))))))))));
    private static Formula FullT(List<DocumentBlock> tables) =>
        Eq(Typed(Call("HardinA229634StripData.T"), Call("Matrix", Fin(33), Fin(33), Call("Int"))), Call("Matrix.reindex", Typed(Call("finSumFinEquiv"), Seq(Call("Fin", Num("20")), Sp, Call("Sum"), Sp, Call("Fin", Num("13")), Sp, Equiv, Sp, Fin(33))), Typed(Call("finSumFinEquiv"), Seq(Call("Fin", Num("20")), Sp, Call("Sum"), Sp, Call("Fin", Num("13")), Sp, Equiv, Sp, Fin(33))), Call("Matrix.fromBlocks" , Call("HardinA229531StripData.T"), Call("Fin.append" , Table(tables, [Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("2"), Num("4"), Num("0"), Num("6"), Num("2"), Num("4"), Num("4"), Num("2")],
            [Num("0"), Num("2"), Num("1"), Num("3"), Num("2"), Num("0"), Num("4"), Num("0"), Num("4"), Num("0"), Num("6"), Num("8"), Num("3")],
            [Num("2"), Num("2"), Num("0"), Num("0"), Num("1"), Num("0"), Num("4"), Num("1"), Num("2"), Num("0"), Num("4"), Num("10"), Num("2")],
            [Num("1"), Num("3"), Num("0"), Num("4"), Num("1"), Num("2"), Num("6"), Num("0"), Num("2"), Num("0"), Num("3"), Num("7"), Num("4")],
            [Num("0"), Num("4"), Num("1"), Num("2"), Num("2"), Num("4"), Num("8"), Num("0"), Num("2"), Num("0"), Num("2"), Num("6"), Num("2")],
            [Num("2"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("0"), Num("4"), Num("0"), Num("4"), Num("12"), Num("4")]), Call("Fin.append" , Call("Matrix.submatrix" , Call("HardinA229634StripData.oldTail"), Fun("i", Fin(6), Add(Call("Fin.val" , V("i")), Num("0"))), Call("id")), Table(tables, [Num("2"), Num("6"), Num("2"), Num("3"), Num("1"), Num("2"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("3"), Num("1")],
            [Num("3"), Num("4"), Num("1"), Num("2"), Num("1"), Num("2"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("3"), Num("1")],
            [Num("0"), Num("2"), Num("2"), Num("2"), Num("1"), Num("2"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("0"), Num("0")],
            [Num("1"), Num("3"), Num("1"), Num("4"), Num("1"), Num("2"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("0"), Num("2")],
            [Num("1"), Num("3"), Num("1"), Num("3"), Num("2"), Num("0"), Num("2"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0")],
            [Num("0"), Num("2"), Num("1"), Num("3"), Num("1"), Num("2"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("1"), Num("0")],
            [Num("1"), Num("1"), Num("1"), Num("3"), Num("2"), Num("0"), Num("2"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0")],
            [Num("0"), Num("2"), Num("2"), Num("2"), Num("1"), Num("2"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("0"), Num("0")]))), Num("0"), Call("Fin.append" , Call("Matrix.submatrix" , Call("HardinA229634StripData.oldTail"), Fun("i", Fin(6), Add(Call("Fin.val" , V("i")), Num("6"))), Call("id")), Vec(Call("HardinA229634StripData.oldTail" , Num("16")), Vec(Num("0"), Num("0"), Num("1"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0")), Call("HardinA229634StripData.oldTail" , Num("13")), Vec(Num("1"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0")), Call("HardinA229634StripData.oldTail" , Num("12")), Call("HardinA229634StripData.oldTail" , Num("14")), Call("HardinA229634StripData.oldTail" , Num("15")))))));
    private static Formula FullInitial() =>
        Eq(Typed(Call("HardinA229634StripData.initial"), new Formula.TypeArrow(Fin(33), Call("Int"))), Call("Fin.append", Call("HardinA229531StripData.initial"), Vec(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("30"), Num("6"), Num("0"), Num("12"), Num("0"), Num("24"), Num("0"))));
    private static Formula FullTerminal() =>
        Eq(Typed(Call("HardinA229634StripData.terminal"), new Formula.TypeArrow(Fin(33), Call("Int"))), Call("Fin.append", Typed(Num("0"), new Formula.TypeArrow(Fin(20), Call("Int"))), Typed(Num("1"), new Formula.TypeArrow(Fin(13), Call("Int")))));
    private static Formula FullW(List<DocumentBlock> tables) =>
        Eq(Typed(Call("HardinA229634StripData.W"), new Formula.TypeArrow(Fin(21), new Formula.TypeArrow(Fin(33), Call("Int")))), Call("Fin.append", Fun("i", Fin(14), Call("Fin.append", Call("HardinA229531StripData.W", V("i")), new Formula.Apply(Table(tables, [Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("30"), Num("6"), Num("0"), Num("12"), Num("0"), Num("24"), Num("0")],
            [Num("168"), Num("396"), Num("168"), Num("396"), Num("198"), Num("204"), Num("264"), Num("6"), Num("204"), Num("12"), Num("264"), Num("456"), Num("192")],
            [Num("4104"), Num("6624"), Num("3444"), Num("5208"), Num("1860"), Num("2868"), Num("1632"), Num("54"), Num("1848"), Num("156"), Num("2376"), Num("4212"), Num("1800")],
            [Num("60864"), Num("97284"), Num("49896"), Num("69732"), Num("22704"), Num("42204"), Num("14232"), Num("480"), Num("18900"), Num("1500"), Num("24600"), Num("44208"), Num("19116")],
            [Num("818808"), Num("1305552"), Num("649698"), Num("880896"), Num("276018"), Num("563340"), Num("130536"), Num("4350"), Num("189900"), Num("14196"), Num("253584"), Num("470340"), Num("204732")],
            [Num("10372524"), Num("16511124"), Num("8022828"), Num("10662660"), Num("3242910"), Num("7105212"), Num("1218408"), Num("40338"), Num("1894308"), Num("134028"), Num("2591400"), Num("4952892"), Num("2165664")],
            [Num("126058428"), Num("200385168"), Num("95508810"), Num("125053632"), Num("37132386"), Num("86092020"), Num("11451816"), Num("378012"), Num("18793692"), Num("1265460"), Num("26288088"), Num("51655344"), Num("22644888")],
            [Num("1485603204"), Num("2359034184"), Num("1106387568"), Num("1431733920"), Num("416763834"), Num("1012629876"), Num("107936880"), Num("3558474"), Num("185784528"), Num("11949180"), Num("265184088"), Num("534131244"), Num("234528492")],
            [Num("17096480808"), Num("27126769416"), Num("12547062444"), Num("16082614596"), Num("4603376772"), Num("11639936196"), Num("1018492872"), Num("33560754"), Num("1831765188"), Num("112836108"), Num("2663101080"), Num("5482472364"), Num("2409867708")],
            [Num("193050744984"), Num("306140334600"), Num("139886100720"), Num("177885607020"), Num("50182685244"), Num("131357287476"), Num("9614928816"), Num("316759884"), Num("18023190336"), Num("1065532596"), Num("26644003248"), Num("55917809856"), Num("24598879008")],
            [Num("2146342936788"), Num("3402355705224"), Num("1537914190518"), Num("1942534928964"), Num("541071639030"), Num("1460123024292"), Num("90785254080"), Num("2990632266"), Num("177024763536"), Num("10062107604"), Num("265708300512"), Num("567210973020"), Num("249682094928")],
            [Num("23556308766720"), Num("37331339165544"), Num("16711271711664"), Num("20985421966716"), Num("5779628845914"), Num("16025809276332"), Num("857269733472"), Num("28239071766"), Num("1736062861584"), Num("95019476052"), Num("2642227523904"), Num("5726243056476"), Num("2521995967020")],
            [Num("255711859899972"), Num("405174631394352"), Num("179792385938598"), Num("224630570251404"), Num("61243171981482"), Num("174005292412164"), Num("8095301613552"), Num("266661283176"), Num("17001558309528"), Num("897298407876"), Num("26207504428776"), Num("57568042110024"), Num("25366203281100")],
            [Num("2749789907518668"), Num("4356566464503588"), Num("1917863490177024"), Num("2385404263597320"), Num("644440881446898"), Num("1871801495581980"), Num("76445865341256"), Num("2518132037430"), Num("166284863868684"), Num("8473472087748"), Num("259345880188512"), Num("576623106792108"), Num("254179646800656")]), [V("i")]))), Table(tables, [Num("377816268254310"), Num("600743597088780"), Num("224555831893872"), Num("257919522373656"), Num("57143078782662"), Num("262936173555204"), Num("3964410013601988"), Num("6273118331236404"), Num("2629397804913408"), Num("3169373717402208"), Num("801222692975520"), Num("2699592780852384"), Num("154888939419840"), Num("74871249978372"), Num("143633364808332"), Num("191192141414088"), Num("0"), Num("143633364808332"), Num("0"), Num("143633364808332"), Num("29328363557493828"), Num("46462937115413520"), Num("20306200339283316"), Num("25155431593951704"), Num("6739782271472796"), Num("19972309696866684"), Num("721900210654944"), Num("23779388302878"), Num("1624418866577160"), Num("80017689441468"), Num("2561076732432936"), Num("5756774027016276"), Num("2538533556212352")],
            [Num("3567839532212298"), Num("5673015341754576"), Num("2120550398541462"), Num("2435612999697780"), Num("539618433050190"), Num("2482992077796588"), Num("40016752044499248"), Num("63340646654601612"), Num("26363434120229256"), Num("31690406664204384"), Num("7956370348888536"), Num("27288304623704352"), Num("1462663722670020"), Num("707031186161400"), Num("1356376133597400"), Num("1805487797385144"), Num("0"), Num("1356376133597400"), Num("0"), Num("1356376133597400"), Num("310563243312713604"), Num("491991684109600068"), Num("213596596127856048"), Num("263653513699563108"), Num("70105198388616720"), Num("211587308140867284"), Num("6817124553451080"), Num("224555831893872"), Num("15851115121270284"), Num("755632536508620"), Num("25242598871144280"), Num("57305030388964320"), Num("25277562373337052")],
            [Num("33692247232519926"), Num("53572101603834552"), Num("20025026636010066"), Num("23000258068758036"), Num("5095781831289432"), Num("23447693903526924"), Num("402250578723172668"), Num("636878660917845252"), Num("263436590697761388"), Num("315892062117033480"), Num("78818905539501348"), Num("274644834239171832"), Num("13812392861205300"), Num("6676713796780704"), Num("12808694406179172"), Num("17049795203262096"), Num("0"), Num("12808694406179172"), Num("0"), Num("12808694406179172"), Num("3267713645334471324"), Num("5176680713716897872"), Num("2233758865680892650"), Num("2748285051878414256"), Num("725687169325679874"), Num("2227373021945726148"), Num("64376246552621544"), Num("2120550398541462"), Num("154514521636897548"), Num("7135679064424596"), Num("248360418587101344"), Num("568931804468937060"), Num("251031172550509428")],
            [Num("318166644053060898"), Num("505898482300303776"), Num("189102689240942004"), Num("217198729140989472"), Num("48121066536057534"), Num("221424085479762804"), Num("4028616164614284792"), Num("6380014356333047964"), Num("2624438106168031128"), Num("3140105669893440360"), Num("779104154423170620"), Num("2753648770441935840"), Num("130434805805818020"), Num("63050311340778168"), Num("120956596068874404"), Num("161006649340894536"), Num("0"), Num("120956596068874404"), Num("0"), Num("120956596068874404"), Num("34187569220817562248"), Num("54160557724327858452"), Num("23239300485687694140"), Num("28507769595593646276"), Num("7479227717518086750"), Num("23314763357106588084"), Num("607925304952321848"), Num("20025026636010066"), Num("1504715920431036396"), Num("67384494465039852"), Num("2439651883683199752"), Num("5634960361904931660"), Num("2486975920924505904")],
            [Num("3004549175342189334"), Num("4777360954955383392"), Num("1785756944565356586"), Num("2051076740242403592"), Num("454422484917989010"), Num("2090978423666254956"), Num("40215807217489068684"), Num("63702557850899068044"), Num("26074516524362429748"), Num("31135958119085466300"), Num("7685879700891067680"), Num("27515366798024284152"), Num("1231737395728995276"), Num("595404107622873480"), Num("1142231770406425572"), Num("1520437148888309580"), Num("0"), Num("1142231770406425572"), Num("0"), Num("1142231770406425572"), Num("355856300861898385272"), Num("563771030532517504608"), Num("240647455056032299890"), Num("294406296196514459184"), Num("76780942897028863962"), Num("242801682490883581548"), Num("5740832169511623816"), Num("189102689240942004"), Num("14639993425051630092"), Num("636333288106121796"), Num("23928963150009194952"), Num("55690239860178034608"), Num("24584588818770106368")],
            [Num("28372916912642961462"), Num("45114144845228427492"), Num("16863472419930867834"), Num("19368971645091260436"), Num("4291256169725749188"), Num("19745777107927655364"), Num("400284414638994582816"), Num("634181252413076589420"), Num("258422334151636967424"), Num("308030631277253263464"), Num("75682813649978725788"), Num("274112644991571075288"), Num("11631688980057495432"), Num("5622590629373116764"), Num("10786459305639762060"), Num("14357973194770475232"), Num("0"), Num("10786459305639762060"), Num("0"), Num("10786459305639762060"), Num("3687040607169827061768"), Num("5841485303653601070792"), Num("2481442327248533863032"), Num("3028253403590875775040"), Num("785407454658131808306"), Num("2516905499803979646444"), Num("54212508620250050880"), Num("1785756944565356586"), Num("142315288533909099864"), Num("6009098350684378668"), Num("234378591948944732664"), Num("549296640099958857084"), Num("242540981865882407052")],
            [Num("267934511129194046202"), Num("426027271948149173376"), Num("159247151325193095708"), Num("182907379140010105332"), Num("40523700234747877458"), Num("186465677731598088636"), Num("3973731007228324719324"), Num("6296795049646520623764"), Num("2555500817493031503456"), Num("3041074241090777843124"), Num("743995757749383307092"), Num("2723348457057190487256"), Num("109841750310238919028"), Num("53095916484952996104"), Num("101859978670514350416"), Num("135586923510376086084"), Num("0"), Num("101859978670514350416"), Num("0"), Num("101859978670514350416"), Num("38041920903512156924028"), Num("60273717355540152964968"), Num("25489303839255020336124"), Num("31035081736087946411652"), Num("8007851252436368678124"), Num("25981205483652482142396"), Num("511946015939562583272"), Num("16863472419930867834"), Num("1382317240450194814836"), Num("56745833825285922924"), Num("2292727820038422899496"), Num("5408118757647961990476"), Num("2388421696545671355204")])));
}
