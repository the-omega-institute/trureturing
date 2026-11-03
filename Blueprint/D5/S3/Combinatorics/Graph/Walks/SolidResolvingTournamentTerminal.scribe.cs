using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class SolidResolvingTournamentTerminalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SolidResolvingTournamentTerminal", H("SolidResolvingTournamentTerminal"), Blocks(
            Describe.Lean(DescribeId.Create("upperofcode"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.upperOfCode"), H("upperOfCode"),
                StatementSource.FromAuthor(Disp(UpperCodeFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural code eight represents infinity. Every other code is its natural-number cast into ENat."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nond30"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD30"), H("nonD30"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD30", [[0, 8, 8], [1, 0, 8], [1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-3-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_3_0"), H("nonstrong profile bound 3 0"),
                StatementSource.FromAuthor(Disp(EnatProfile(3, "nonD30", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond40"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD40"), H("nonD40"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD40", [[0, 8, 8, 8], [1, 0, 8, 8], [1, 1, 0, 8], [1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-4-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_0"), H("nonstrong profile bound 4 0"),
                StatementSource.FromAuthor(Disp(EnatProfile(4, "nonD40", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond42"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD42"), H("nonD42"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD42", [[0, 2, 1, 8], [1, 0, 2, 8], [2, 1, 0, 8], [1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-4-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_2"), H("nonstrong profile bound 4 2"),
                StatementSource.FromAuthor(Disp(EnatProfile(4, "nonD42", true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond45"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD45"), H("nonD45"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD45", [[0, 1, 2, 1], [8, 0, 8, 8], [1, 1, 0, 2], [2, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-4-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_5"), H("nonstrong profile bound 4 5"),
                StatementSource.FromAuthor(Disp(EnatProfile(4, "nonD45", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond50"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD50"), H("nonD50"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD50", [[0, 8, 8, 8, 8], [1, 0, 8, 8, 8], [1, 1, 0, 8, 8], [1, 1, 1, 0, 8], [1, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-5-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_0"), H("nonstrong profile bound 5 0"),
                StatementSource.FromAuthor(Disp(EnatProfile(5, "nonD50", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond52"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD52"), H("nonD52"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD52", [[0, 2, 1, 8, 8], [1, 0, 2, 8, 8], [2, 1, 0, 8, 8], [1, 1, 1, 0, 8], [1, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-5-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_2"), H("nonstrong profile bound 5 2"),
                StatementSource.FromAuthor(Disp(EnatProfile(5, "nonD52", true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond54"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD54"), H("nonD54"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD54", [[0, 2, 2, 1, 8], [1, 0, 3, 2, 8], [1, 1, 0, 2, 8], [2, 1, 1, 0, 8], [1, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-5-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_4"), H("nonstrong profile bound 5 4"),
                StatementSource.FromAuthor(Disp(EnatProfile(5, "nonD54", true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond55"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD55"), H("nonD55"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD55", [[0, 1, 2, 1, 8], [8, 0, 8, 8, 8], [1, 1, 0, 2, 8], [2, 1, 1, 0, 8], [1, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-5-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_5"), H("nonstrong profile bound 5 5"),
                StatementSource.FromAuthor(Disp(EnatProfile(5, "nonD55", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond59"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD59"), H("nonD59"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD59", [[0, 1, 2, 2, 1], [8, 0, 8, 8, 8], [1, 1, 0, 3, 2], [1, 1, 1, 0, 2], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-5-9"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_9"), H("nonstrong profile bound 5 9"),
                StatementSource.FromAuthor(Disp(EnatProfile(5, "nonD59", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nond511"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD511"), H("nonD511"),
                StatementSource.FromAuthor(Disp(MatrixFormula("nonD511", [[0, 1, 1, 2, 1], [8, 0, 8, 8, 8], [8, 1, 0, 8, 8], [1, 1, 1, 0, 2], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonstrong-profile-bound-5-11"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_11"), H("nonstrong profile bound 5 11"),
                StatementSource.FromAuthor(Disp(EnatProfile(5, "nonD511", false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-3-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_3_0"), H("nonstrong antichain bound 3 0"),
                StatementSource.FromAuthor(Disp(AntichainBound(3, "nonD30", 1, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-4-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_0"), H("nonstrong antichain bound 4 0"),
                StatementSource.FromAuthor(Disp(AntichainBound(4, "nonD40", 2, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-4-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_2"), H("nonstrong antichain bound 4 2"),
                StatementSource.FromAuthor(Disp(AntichainBound(4, "nonD42", 2, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-4-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_5"), H("nonstrong antichain bound 4 5"),
                StatementSource.FromAuthor(Disp(AntichainBound(4, "nonD45", 2, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-5-0"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_0"), H("nonstrong antichain bound 5 0"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "nonD50", 5, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-5-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_2"), H("nonstrong antichain bound 5 2"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "nonD52", 5, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-5-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_4"), H("nonstrong antichain bound 5 4"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "nonD54", 5, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-5-5"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_5"), H("nonstrong antichain bound 5 5"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "nonD55", 5, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-5-9"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_9"), H("nonstrong antichain bound 5 9"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "nonD59", 5, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonstrong-antichain-bound-5-11"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_11"), H("nonstrong antichain bound 5 11"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "nonD511", 5, true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-enat-profile-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.strong_enat_profile_bound"), H("strong enat profile bound"),
                StatementSource.FromAuthor(Disp(StrongEnatFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite landmark upper bounds make the entire extended-natural profile finite. The corresponding natural-profile estimate then bounds every original coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("card-bound-of-profile-model"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.card_bound_of_profile_model"), H("card bound of profile model"),
                StatementSource.FromAuthor(Disp(ProfileModelFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vertices outside the landmarks have mutually incomparable positive distance profiles. A bound on the cardinality of these profiles adds to the number of landmarks to bound the ambient order."))), DescribeRole.Theorem))));
    private static Formula X(string n) => F.Id(n);

    private static Formula N(int n) => new Formula.Number(n);

    private static Formula Q(string o, string n) => Seq(Operatorname, Grp(X(o)), Dot, Operatorname, Grp(X(n)));

    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);

    private static Formula Call(string f, params Formula[] xs) => xs.Length == 0 ? Seq(Operatorname, Grp(X(f))) : App(Seq(Operatorname, Grp(X(f))), xs);

    private static Formula P(Formula p) => Parenthesized(p);

    private static Formula Parenthesized(Formula p) => Seq(Left, Open, p, Right, Close);

    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);

    private static Formula Ex(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);

    private static Formula A(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);

    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula EqF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.Equal, q);

    private static Formula Ne(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.NotEqual, q);

    private static Formula LeF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, q);

    private static Formula LtF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.LessThan, q);

    private static Formula NotF(Formula p) => Seq(Neg, Sp, P(p));

    private static Formula Add(Formula p, Formula q) => new Formula.Binary(p, FormulaBinaryOperator.Add, q);

    private static Formula Arr(Formula a, Formula b) => Seq(P(a), Sp, To, Sp, P(b));

    private static Formula NatT() => Call("Nat");

    private static Formula ENatT() => Call("ENat");

    private static Formula TypeT() => X("Type");

    private static Formula FinT(Formula k) => Call("Fin", k);

    private static Formula Inst(string n, Formula t) => Seq(OpenBracket, Call(n, t), CloseBracket, Sp);

    private static Formula At(Formula f, params Formula[] xs) => App(P(f), xs);

    private static Formula DD(Formula r, Formula a, Formula b) => Call("directedDistance", r, a, b);

    private static Formula Cast(Formula a, Formula t) => P(Seq(a, Sp, Colon, Sp, t));

    private static Formula Range(Formula l) => App(Q("Set", "range"), l);

    private static Formula Solid(Formula r, Formula s) => Call("IsSolidResolving", r, s);

    private static Formula Card(Formula u) => App(Q("Fintype", "card"), u);

    private static Formula ForIJ(Formula k, Formula p) => All("i", FinT(k), All("j", FinT(k), p));

    private static Formula Pos(Formula k, Formula x) => All("i", FinT(k), LeF(N(1), At(x, X("i"))));

    private static Formula B(Formula k, Formula d, Formula x) => All("j", FinT(k), Ex("i", FinT(k), LtF(At(x, X("i")), At(d, X("i"), X("j")))));

    private static Formula C(Formula k, Formula d, Formula x) => ForIJ(k, LeF(At(x, X("i")), Add(At(d, X("i"), X("j")), At(x, X("j")))));

    private static Formula Bound(Formula k, Formula x, int b) => All("i", FinT(k), LeF(At(x, X("i")), N(b)));

    private static Formula Anti(Formula u, Formula f) => All("a", u, All("b", u, Imp(Ne(X("a"), X("b")), A(NotF(LeF(At(f, X("a")), At(f, X("b")))), NotF(LeF(At(f, X("b")), At(f, X("a"))))))));

    private static Formula Code(Formula d) => Call("upperOfCode", d);

    private static Formula EnatProfile(int k, string d, bool triangles)
    {
        Formula body=Bound(N(k), X("x"), 2);
        if(triangles) body=Imp(C(N(k), Code(X(d)), X("x")),body);
        return All("x", Arr(FinT(N(k)), ENatT()), Imp(Pos(N(k), X("x")), Imp(B(N(k), Code(X(d)), X("x")), body)));
    }

    private static Formula AntichainBound(int k, string d, int c, bool bounded)
    {
        Formula f = X("f"), u = X("U"), z = X("u");
        Formula body = Imp(All("u", u, Pos(N(k), At(f, z))), Imp(All("u", u, B(N(k), X(d), At(f, z))), Imp(All("u", u, C(N(k), X(d), At(f, z))), Imp(Anti(u, f), LeF(Card(u), N(c))))));
        if (bounded) body = Imp(All("u", u, Bound(N(k), At(f, z), 2)), body);
        return All("U", TypeT(), Seq(Inst("Fintype", u), All("f", Arr(u, Arr(FinT(N(k)), NatT())), body)));
    }

    private static Formula Vec(params Formula[] items) => Seq(Bang, OpenBracket, Join(items), CloseBracket);

    private static Formula Join(Formula[] items)
    {
        if (items.Length == 0) return Seq();
        Formula value = items[0];
        for (int i = 1; i < items.Length; i++) value = Seq(value, Comma, Sp, items[i]);
        return value;
    }

    private static Formula MatrixFormula(string name, int[][] entries)
    {
        var rows = new Formula[entries.Length];
        for (int i = 0; i < entries.Length; i++)
        {
            var row = new Formula[entries[i].Length];
            for (int j = 0; j < row.Length; j++) row[j] = N(entries[i][j]);
            rows[i] = Vec(row);
        }
        return EqF(Cast(X(name), Arr(FinT(N(entries.Length)), Arr(FinT(N(entries.Length)), NatT()))), Vec(rows));
    }

    private static Formula UpperCodeFormula()
    {
        Formula i=X("i"),j=X("j"),d=X("D"),t=X("I");
        return All("I",TypeT(),All("D",Arr(t,Arr(t,NatT())),All("i",t,All("j",t,EqF(Call("upperOfCode",d,i,j),Call("ite",EqF(At(d,i,j),N(8)),Seq(Infty),Cast(At(d,i,j),ENatT())))))));
    }

    private static Formula StrongEnatFormula()
    {
        Formula k=X("k"),d=X("D"),x=X("x"),y=X("y");
        Formula nb=All("y",Arr(FinT(k),NatT()),Imp(Pos(k,y),Imp(B(k,d,y),Imp(C(k,d,y),Bound(k,y,2)))));
        return All("k",NatT(),All("D",Arr(FinT(k),Arr(FinT(k),NatT())),Imp(ForIJ(k,LeF(At(d,X("i"),X("j")),N(4))),Arr(FinT(k),Imp(nb,All("x",Arr(FinT(k),ENatT()),Imp(Pos(k,x),Imp(B(k,Code(d),x),Imp(C(k,Code(d),x),Bound(k,x,2))))))))));
    }

    private static Formula ProfileModelFormula()
    {
        Formula v=X("V"),k=X("k"),c=X("c"),r=X("R"),l=X("L"),d=X("D"),x=X("x"),u=X("U"),f=X("f"),z=X("u");
        Formula hd=ForIJ(k,LeF(DD(r,At(l,X("i")),At(l,X("j"))),Call("upperOfCode",d,X("i"),X("j"))));
        Formula hb=All("x",Arr(FinT(k),ENatT()),Imp(Pos(k,x),Imp(B(k,Code(d),x),Imp(C(k,Code(d),x),Bound(k,x,2)))));
        Formula hw=All("U",TypeT(),Seq(Inst("Fintype",u),All("f",Arr(u,Arr(FinT(k),NatT())),Imp(All("u",u,Bound(k,At(f,z),2)),Imp(All("u",u,Pos(k,At(f,z))),Imp(All("u",u,B(k,d,At(f,z))),Imp(All("u",u,C(k,d,At(f,z))),Imp(Anti(u,f),LeF(Card(u),c)))))))));
        return All("V",TypeT(),Seq(Inst("Fintype",v),All("k",NatT(),All("c",NatT(),All("R",Arr(v,Arr(v,X("Prop"))),All("L",Arr(FinT(k),v),Imp(App(Q("Function","Injective"),l),Imp(Solid(r,Range(l)),All("D",Arr(FinT(k),Arr(FinT(k),NatT())),Imp(hd,Imp(hb,Imp(hw,LeF(Card(v),Add(k,c))))))))))))));
    }

}
