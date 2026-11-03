using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class SolidResolvingTournamentProfilesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SolidResolvingTournamentProfiles", H("SolidResolvingTournamentProfiles"), Blocks(
            Describe.Lean(DescribeId.Create("card-le-of-chain-cover"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.card_le_of_chain_cover"), H("card le of chain cover"),
                StatementSource.FromAuthor(Disp(ChainCoverFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assigning an incomparable element to a chain containing its image is injective. Therefore the number of elements is at most the number of covering chains."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("profile-finite-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.profile_finite_bound"), H("profile finite bound"),
                StatementSource.FromAuthor(Disp(FiniteProfileFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One strict column inequality makes one coordinate finite; the triangle inequalities then make every coordinate finite and at most twice R minus one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d32"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D32"), H("D32"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D32", [[0, 2, 1], [1, 0, 2], [2, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-3-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_3_2"), H("nat profile bound 3 2"),
                StatementSource.FromAuthor(Disp(NatProfile(3, "D32"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d44"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D44"), H("D44"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D44", [[0, 2, 2, 1], [1, 0, 3, 2], [1, 1, 0, 2], [2, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-4-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_4_4"), H("nat profile bound 4 4"),
                StatementSource.FromAuthor(Disp(NatProfile(4, "D44"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d58"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D58"), H("D58"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D58", [[0, 2, 2, 2, 1], [1, 0, 3, 3, 2], [1, 1, 0, 3, 2], [1, 1, 1, 0, 2], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-5-8"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_8"), H("nat profile bound 5 8"),
                StatementSource.FromAuthor(Disp(NatProfile(5, "D58"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d510"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D510"), H("D510"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D510", [[0, 2, 1, 2, 1], [1, 0, 2, 3, 2], [2, 1, 0, 4, 3], [1, 1, 1, 0, 2], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-5-10"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_10"), H("nat profile bound 5 10"),
                StatementSource.FromAuthor(Disp(NatProfile(5, "D510"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d512"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D512"), H("D512"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D512", [[0, 2, 2, 1, 1], [1, 0, 3, 2, 2], [1, 1, 0, 2, 2], [2, 1, 1, 0, 3], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-5-12"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_12"), H("nat profile bound 5 12"),
                StatementSource.FromAuthor(Disp(NatProfile(5, "D512"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d540"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D540"), H("D540"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D540", [[0, 2, 2, 2, 1], [1, 0, 2, 1, 2], [1, 1, 0, 2, 2], [1, 2, 1, 0, 2], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-5-40"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_40"), H("nat profile bound 5 40"),
                StatementSource.FromAuthor(Disp(NatProfile(5, "D540"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d541"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D541"), H("D541"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D541", [[0, 1, 2, 2, 1], [2, 0, 2, 1, 3], [1, 1, 0, 2, 2], [1, 2, 1, 0, 2], [2, 1, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-5-41"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_41"), H("nat profile bound 5 41"),
                StatementSource.FromAuthor(Disp(NatProfile(5, "D541"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("d576"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D576"), H("D576"),
                StatementSource.FromAuthor(Disp(MatrixFormula("D576", [[0, 2, 2, 1, 1], [1, 0, 2, 2, 1], [1, 1, 0, 2, 2], [2, 1, 1, 0, 2], [2, 2, 1, 1, 0]]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nat-profile-bound-5-76"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_76"), H("nat profile bound 5 76"),
                StatementSource.FromAuthor(Disp(NatProfile(5, "D576"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The necessary inequalities for an outside distance profile force every coordinate to be at most two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("acbool"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.acBool"), H("acBool"),
                StatementSource.FromAuthor(Disp(ACBoolFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Boolean test is the conjunction of positivity, a strict comparison in every landmark column, and every triangle upper bound."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("profile-mem-of-certificate"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.profile_mem_of_certificate"), H("profile mem of certificate"),
                StatementSource.FromAuthor(Disp(ProfileMemFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A certificate listing all bounded positive profiles supplies a listed Fin-valued representative of every natural profile satisfying the same inequalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cardinal-le-profile-chains"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.cardinal_le_profile_chains"), H("cardinal le profile chains"),
                StatementSource.FromAuthor(Disp(CardinalChainsFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite list of chains covering the natural profiles bounds the cardinality of any mutually incomparable family of those profiles."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-3-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_3_2"), H("strong profile antichain bound 3 2"),
                StatementSource.FromAuthor(Disp(AntichainBound(3, "D32", 1, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-4-4"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_4_4"), H("strong profile antichain bound 4 4"),
                StatementSource.FromAuthor(Disp(AntichainBound(4, "D44", 2, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-5-8"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_8"), H("strong profile antichain bound 5 8"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "D58", 5, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-5-10"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_10"), H("strong profile antichain bound 5 10"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "D510", 5, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-5-12"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_12"), H("strong profile antichain bound 5 12"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "D512", 5, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-5-40"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_40"), H("strong profile antichain bound 5 40"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "D540", 5, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-5-41"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_41"), H("strong profile antichain bound 5 41"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "D541", 5, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strong-profile-antichain-bound-5-76"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_76"), H("strong profile antichain bound 5 76"),
                StatementSource.FromAuthor(Disp(AntichainBound(5, "D576", 5, false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two."))), DescribeRole.Theorem))));
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

    private static Formula O(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Or, q);

    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula EqF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.Equal, q);

    private static Formula Ne(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.NotEqual, q);

    private static Formula LeF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, q);

    private static Formula LtF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.LessThan, q);

    private static Formula Mem(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.MemberOf, q);

    private static Formula NotF(Formula p) => Seq(Neg, Sp, P(p));

    private static Formula Add(Formula p, Formula q) => new Formula.Binary(p, FormulaBinaryOperator.Add, q);

    private static Formula Sub(Formula p, Formula q) => new Formula.Binary(p, FormulaBinaryOperator.Subtract, q);

    private static Formula Mul(Formula p, Formula q) => new Formula.Binary(p, FormulaBinaryOperator.Multiply, q);

    private static Formula Arr(Formula a, Formula b) => Seq(P(a), Sp, To, Sp, P(b));

    private static Formula NatT() => Call("Nat");

    private static Formula ENatT() => Call("ENat");

    private static Formula TypeT() => X("Type");

    private static Formula FinT(Formula k) => Call("Fin", k);

    private static Formula Inst(string n, Formula t) => Seq(OpenBracket, Call(n, t), CloseBracket, Sp);

    private static Formula Lam(string n, Formula t, Formula p) => Seq(X("fun"), Sp, P(Seq(X(n), Colon, Sp, t)), Sp, Mapsto, Sp, p);

    private static Formula At(Formula f, params Formula[] xs) => App(P(f), xs);

    private static Formula Val(Formula a) => Call("val", a);

    private static Formula Cast(Formula a, Formula t) => P(Seq(a, Sp, Colon, Sp, t));

    private static Formula Card(Formula u) => App(Q("Fintype", "card"), u);

    private static Formula ListT(Formula t) => Call("List", t);

    private static Formula ForIJ(Formula k, Formula p) => All("i", FinT(k), All("j", FinT(k), p));

    private static Formula Pos(Formula k, Formula x) => All("i", FinT(k), LeF(N(1), At(x, X("i"))));

    private static Formula B(Formula k, Formula d, Formula x) => All("j", FinT(k), Ex("i", FinT(k), LtF(At(x, X("i")), At(d, X("i"), X("j")))));

    private static Formula C(Formula k, Formula d, Formula x) => ForIJ(k, LeF(At(x, X("i")), Add(At(d, X("i"), X("j")), At(x, X("j")))));

    private static Formula Bound(Formula k, Formula x, int b) => All("i", FinT(k), LeF(At(x, X("i")), N(b)));

    private static Formula Anti(Formula u, Formula f) => All("a", u, All("b", u, Imp(Ne(X("a"), X("b")), A(NotF(LeF(At(f, X("a")), At(f, X("b")))), NotF(LeF(At(f, X("b")), At(f, X("a"))))))));

    private static Formula NatProfile(int k, string d) => All("x", Arr(FinT(N(k)), NatT()), Imp(Pos(N(k), X("x")), Imp(B(N(k), X(d), X("x")), Imp(C(N(k), X(d), X("x")), Bound(N(k), X("x"), 2)))));

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

    private static Formula AllList(Formula p, Formula l) => App(Q("List", "all"), l, p);

    private static Formula AnyList(Formula p, Formula l) => App(Q("List", "any"), l, p);


    private static Formula ChainCoverFormula()
    {
        Formula u = X("U"), p = X("P"), f = X("f"), cs = X("chains"), m = X("m");
        Formula cover = All("u", u, Ex("i", FinT(m), Mem(At(f, X("u")), At(cs, X("i")))));
        Formula chain = All("i", FinT(m), All("a", p, All("b", p, Imp(Mem(X("a"), At(cs, X("i"))), Imp(Mem(X("b"), At(cs, X("i"))), O(LeF(X("a"), X("b")), LeF(X("b"), X("a"))))))));
        return All("U", TypeT(), All("P", TypeT(), Seq(Inst("Fintype", u), Inst("Preorder", p), All("f", Arr(u, p), All("m", NatT(), All("chains", Arr(FinT(m), Call("Set", p)), Imp(cover, Imp(chain, Imp(Anti(u, f), LeF(Card(u), m))))))))));
    }

    private static Formula FiniteProfileFormula()
    {
        Formula k=X("k"),r=X("R"),d=X("D"),x=X("x"),y=X("y");
        Formula dc=Lam("i",FinT(k),Lam("j",FinT(k),Cast(At(d,X("i"),X("j")),ENatT())));
        Formula outp=Ex("y",Arr(FinT(k),NatT()),A(All("i",FinT(k),EqF(Cast(At(y,X("i")),ENatT()),At(x,X("i")))),All("i",FinT(k),LeF(At(y,X("i")),Sub(Mul(N(2),r),N(1))))));
        return All("k",NatT(),All("R",NatT(),All("D",Arr(FinT(k),Arr(FinT(k),NatT())),Imp(ForIJ(k,LeF(At(d,X("i"),X("j")),r)),Arr(FinT(k),All("x",Arr(FinT(k),ENatT()),Imp(B(k,dc,x),Imp(C(k,dc,x),outp))))))));
    }

    private static Formula ACBoolFormula()
    {
        Formula k=X("k"),b=X("b"),d=X("D"),x=X("x");
        Formula FR()=>App(Q("List","finRange"),k);
        Formula ListAll(string n,Formula p)=>AllList(Lam(n,FinT(k),p),FR());
        Formula ListAny(string n,Formula p)=>AnyList(Lam(n,FinT(k),p),FR());
        Formula xp(Formula i)=>Val(At(x,i));
        Formula a=ListAll("i",Call("decide",LeF(N(1),xp(X("i")))));
        Formula bb=ListAll("j",ListAny("i",Call("decide",LtF(xp(X("i")),At(d,X("i"),X("j"))))));
        Formula c=ListAll("i",ListAll("j",Call("decide",LeF(xp(X("i")),Add(At(d,X("i"),X("j")),xp(X("j")))))));
        return All("k",NatT(),All("b",NatT(),All("D",Arr(FinT(k),Arr(FinT(k),NatT())),All("x",Arr(FinT(k),FinT(b)),EqF(Call("acBool",d,x),App(Q("Bool","and"),App(Q("Bool","and"),a,bb),c))))));
    }

    private static Formula ProfileMemFormula()
    {
        Formula k=X("k"),d=X("D"),ps=X("ps"),y=X("y"),x=X("x"),ft=Arr(FinT(k),FinT(N(3)));
        Formula cert=EqF(AllList(Lam("x",ft,App(Q("Bool","or"),App(Q("Bool","not"),Call("acBool",d,x)),Call("decide",Mem(x,ps)))),Call("enumTuple",App(Q("List","finRange"),N(3)),k)),X("true"));
        Formula outp=Ex("x",ft,A(All("i",FinT(k),EqF(Val(At(x,X("i"))),At(y,X("i")))),Mem(x,ps)));
        return All("k",NatT(),All("D",Arr(FinT(k),Arr(FinT(k),NatT())),All("ps",ListT(ft),Imp(cert,All("y",Arr(FinT(k),NatT()),Imp(All("i",FinT(k),LtF(At(y,X("i")),N(3))),Imp(Pos(k,y),Imp(B(k,d,y),Imp(C(k,d,y),outp)))))))));
    }

    private static Formula CardinalChainsFormula()
    {
        Formula u=X("U"),k=X("k"),f=X("f"),cs=X("chains"),ft=Arr(FinT(k),FinT(N(3))),t=ListT(ft);
        Formula cover=All("u",u,Ex("z",ft,A(All("j",FinT(k),EqF(Val(At(X("z"),X("j"))),At(f,X("u"),X("j")))),Mem(X("z"),App(Q("List","flatten"),cs)))));
        Formula comp=O(All("j",FinT(k),LeF(Val(At(X("a"),X("j"))),Val(At(X("b"),X("j"))))),All("j",FinT(k),LeF(Val(At(X("b"),X("j"))),Val(At(X("a"),X("j"))))));
        Formula chain=All("ch",t,Imp(Mem(X("ch"),cs),All("a",ft,Imp(Mem(X("a"),X("ch")),All("b",ft,Imp(Mem(X("b"),X("ch")),comp))))));
        return All("U",TypeT(),Seq(Inst("Fintype",u),All("k",NatT(),All("f",Arr(u,Arr(FinT(k),NatT())),All("chains",ListT(t),Imp(cover,Imp(chain,Imp(Anti(u,f),LeF(Card(u),App(Q("List","length"),cs))))))))));
    }


}
