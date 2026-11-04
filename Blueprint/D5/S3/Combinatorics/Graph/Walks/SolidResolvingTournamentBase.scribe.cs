using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class SolidResolvingTournamentBaseDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ConceptDynamics/hakanenpavan2026solid");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SolidResolvingTournamentBase", H("SolidResolvingTournamentBase"), Blocks(
            Describe.Lean(DescribeId.Create("directeddistance"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.directedDistance"), H("directedDistance"),
                StatementSource.FromAuthor(Disp(DirectedDistanceFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The distance from u to v is defined as the number of arcs in a shortest directed path from u to v, and is denoted by d_D(u, v) (where the subscript D may be omitted if the context is clear). If no such directed path exists, then v is not reachable from u, and d(u, v) = ∞. (Page 3.) The infimum of directed walk lengths has this value, with the empty infimum equal to infinity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("distancetoset"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.distanceToSet"), H("distanceToSet"),
                StatementSource.FromAuthor(Disp(DistanceSetFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The distance from a vertex u to a vertex set X ⊆ V(D) is defined as d(u, X) = min_{x ∈ X} d(u, x). If no directed path exists from u to any vertex in X, then d(u, X) = ∞. (Page 3.) The displayed infimum uses the subtype of vertices in X."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("issolidresolving"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.IsSolidResolving"), H("IsSolidResolving"),
                StatementSource.FromAuthor(Disp(SolidFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let D be a digraph. A set S ⊆ V(D) is a solid-resolving set of D if for every vertex v ∈ V(D) and every non-empty subset X ⊆ V(D) with X ≠ {v}, there exists w ∈ S such that d(w, v) ≠ d(w, X). The minimum cardinality of a solid-resolving set is called the solid-metric dimension of D, and is denoted by βₛ(D). (Definition 1.1, page 3.) Vertices range over V; R is the arc relation; X and S are vertex sets. Every nonempty X other than the singleton is retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("solidmetricdimension"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.solidMetricDimension"), H("solidMetricDimension"),
                StatementSource.FromAuthor(Disp(DimensionFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let D be a digraph. A set S ⊆ V(D) is a solid-resolving set of D if for every vertex v ∈ V(D) and every non-empty subset X ⊆ V(D) with X ≠ {v}, there exists w ∈ S such that d(w, v) ≠ d(w, X). The minimum cardinality of a solid-resolving set is called the solid-metric dimension of D, and is denoted by βₛ(D). (Definition 1.1, page 3.) The minimum is the natural infimum of cardinalities of finite solid sets. The full vertex set is solid."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("solid-iff-ordered"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.solid_iff_ordered"), H("solid iff ordered"),
                StatementSource.FromAuthor(Disp(OrderedFormula())), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let D be a nontrivial digraph. A set S ⊆ V(D) is a solid-resolving set of D if and only if for all distinct u, v ∈ V(D), there is an element s ∈ S such that d(s, u) < d(s, v). (Theorem 2.1, page 3.)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("profile-constraints"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.profile_constraints"), H("profile constraints"),
                StatementSource.FromAuthor(Disp(ProfileConstraintsFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distance profile of a vertex outside the landmarks is positive, lies below some landmark distance in each column, and satisfies every triangle upper bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pairindex"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.pairIndex"), H("pairIndex"),
                StatementSource.FromAuthor(Disp(PairIndexFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The index of the unordered pair with i less than j in the row-major upper triangle. Nat.div is truncated natural-number division, and natural subtraction truncates at zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maskarc"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.maskArc"), H("maskArc"),
                StatementSource.FromAuthor(Disp(MaskArcFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A mask bit directs the arc from the smaller index to the larger index; the reverse arc uses its Boolean negation and diagonal entries are false."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("walkbound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.walkBound"), H("walkBound"),
                StatementSource.FromAuthor(Disp(WalkBoundFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Boolean recurrence tests reachability by at most n arcs, allowing an empty walk when its two endpoints coincide."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("directeddistance-le-walkbound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.directedDistance_le_walkBound"), H("directedDistance le walkBound"),
                StatementSource.FromAuthor(Disp(WalkUpperFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed formula specifies the object and all of its parameters."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dimension-lower-of-fixed-card-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase.dimension_lower_of_fixed_card_bound"), H("dimension lower of fixed card bound"),
                StatementSource.FromAuthor(Disp(DimensionLowerFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A smaller solid set can be enlarged to cardinality k. If every solid set of that cardinality forces an ambient order at most c, an ambient order greater than c has solid-metric dimension at least k plus one."))), DescribeRole.Theorem))));
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

    private static Formula IffF(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Iff, q);

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

    private static Formula DD(Formula r, Formula a, Formula b) => Call("directedDistance", r, a, b);

    private static Formula Val(Formula a) => Call("val", a);

    private static Formula Cast(Formula a, Formula t) => P(Seq(a, Sp, Colon, Sp, t));

    private static Formula Range(Formula l) => App(Q("Set", "range"), l);

    private static Formula Solid(Formula r, Formula s) => Call("IsSolidResolving", r, s);

    private static Formula Card(Formula u) => App(Q("Fintype", "card"), u);

    private static Formula ForIJ(Formula k, Formula p) => All("i", FinT(k), All("j", FinT(k), p));

    private static Formula Pos(Formula k, Formula x) => All("i", FinT(k), LeF(N(1), At(x, X("i"))));

    private static Formula B(Formula k, Formula d, Formula x) => All("j", FinT(k), Ex("i", FinT(k), LtF(At(x, X("i")), At(d, X("i"), X("j")))));

    private static Formula C(Formula k, Formula d, Formula x) => ForIJ(k, LeF(At(x, X("i")), Add(At(d, X("i"), X("j")), At(x, X("j")))));

    private static Formula AnyList(Formula p, Formula l) => App(Q("List", "any"), l, p);


    private static Formula DirectedDistanceFormula()
    {
        Formula v = X("V"), r = X("R"), a = X("u"), b = X("v");
        Formula q = Seq(Langle, Sp, Lam("a", v, Lam("b", v, Call("PLift", At(r, X("a"), X("b"))))), Rangle);
        Formula length = App(Seq(Q("Quiver", "Path"), Dot, Operatorname, Grp(X("length"))), X("p"));
        Formula rhs = Seq(X("letI"), Sp, Colon, Sp, Call("Quiver", v), Sp, Colon, Eq, Sp, q, Semi, Sp,
            Call("iInf", Lam("p", App(Q("Quiver", "Path"), a, b), Cast(length, ENatT()))));
        return All("V", TypeT(), All("R", Arr(v, Arr(v, X("Prop"))), All("u", v, All("v", v, EqF(DD(r, a, b), rhs)))));
    }

    private static Formula DistanceSetFormula() => All("V", TypeT(), All("R", Arr(X("V"), Arr(X("V"), X("Prop"))), All("u", X("V"), All("X", Call("Set", X("V")), EqF(Call("distanceToSet", X("R"), X("u"), X("X")), Call("iInf", Lam("v", X("X"), DD(X("R"), X("u"), Val(X("v"))))))))));

    private static Formula SolidFormula()
    {
        Formula rhs = All("v", X("V"), All("X", Call("Set", X("V")), Imp(App(Q("Set", "Nonempty"), X("X")), Imp(Ne(X("X"), Seq(OpenBrace, X("v"), CloseBrace)), Ex("w", X("V"), A(Mem(X("w"), X("S")), Ne(DD(X("R"), X("w"), X("v")), Call("distanceToSet", X("R"), X("w"), X("X")))))))));
        return All("V", TypeT(), All("R", Arr(X("V"), Arr(X("V"), X("Prop"))), All("S", Call("Set", X("V")), EqF(Solid(X("R"), X("S")), rhs))));
    }

    private static Formula DimensionFormula()
    {
        Formula rhs = Call("sInf", Seq(OpenBrace, X("k"), Colon, Sp, NatT(), Sp, Bar, Sp, Ex("S", Call("Finset", X("V")), A(Solid(X("R"), Cast(X("S"), Call("Set", X("V")))), EqF(App(Q("Finset", "card"), X("S")), X("k")))), CloseBrace));
        return All("V", TypeT(), Seq(Inst("Fintype", X("V")), All("R", Arr(X("V"), Arr(X("V"), X("Prop"))), EqF(Call("solidMetricDimension", X("R")), rhs))));
    }

    private static Formula OrderedFormula()
    {
        Formula rhs = All("u", X("V"), All("v", X("V"), Imp(Ne(X("u"), X("v")), Ex("w", X("V"), A(Mem(X("w"), X("S")), LtF(DD(X("R"), X("w"), X("u")), DD(X("R"), X("w"), X("v"))))))));
        return All("V", TypeT(), All("R", Arr(X("V"), Arr(X("V"), X("Prop"))), All("S", Call("Set", X("V")), IffF(Solid(X("R"), X("S")), rhs))));
    }

    private static Formula ProfileConstraintsFormula()
    {
        Formula v = X("V"), k = X("k"), r = X("R"), l = X("L"), d = X("D"), u = X("u");
        Formula x = Lam("a", FinT(k), DD(r, At(l, X("a")), u));
        Formula hd = ForIJ(k, LeF(DD(r, At(l, X("i")), At(l, X("j"))), At(d, X("i"), X("j"))));
        return All("V", TypeT(), Seq(All("k", NatT(), All("R", Arr(v, Arr(v, X("Prop"))), All("L", Arr(FinT(k), v), Imp(Solid(r, Range(l)), All("u", v, Imp(NotF(Mem(u, Range(l))), All("D", Arr(FinT(k), Arr(FinT(k), ENatT())), Imp(hd, A(Pos(k, x), A(B(k, d, x), C(k, d, x)))))))))))));
    }

    private static Formula PairIndexFormula()
    {
        Formula k=X("k"), i=X("i"), j=X("j");
        return All("k", NatT(), All("i", NatT(), All("j", NatT(), EqF(Call("pairIndex", k, i, j), Add(App(Q("Nat", "div"), Mul(i, P(Sub(Sub(Mul(N(2), k), i), N(1)))), N(2)), P(Sub(Sub(j, i), N(1))))))));
    }

    private static Formula MaskArcFormula()
    {
        Formula k=X("k"), m=X("m"), i=X("i"), j=X("j");
        Formula Bit(Formula a,Formula b) => App(Q("Nat", "testBit"), m, Call("pairIndex", k, Val(a), Val(b)));
        Formula rhs=Call("ite", LtF(Val(i),Val(j)), Bit(i,j), Call("ite", LtF(Val(j),Val(i)), App(Q("Bool", "not"),Bit(j,i)), X("false")));
        return All("k", NatT(), All("m", NatT(), All("i", FinT(k), All("j", FinT(k), EqF(Call("maskArc",m,i,j),rhs)))));
    }

    private static Formula WalkBoundFormula()
    {
        Formula k=X("k"),m=X("m"),i=X("i"),j=X("j"),n=X("n");
        Formula zero=ForIJ(k,EqF(Call("walkBound",m,N(0),i,j),App(Q("BEq","beq"),i,j)));
        Formula rhs=App(Q("Bool","or"),Call("walkBound",m,n,i,j), AnyList(Lam("z",FinT(k),App(Q("Bool","and"),Call("walkBound",m,n,i,X("z")),Call("maskArc",m,X("z"),j))),App(Q("List","finRange"),k)));
        return All("k",NatT(),All("m",NatT(),A(zero,All("n",NatT(),ForIJ(k,EqF(Call("walkBound",m,Add(n,N(1)),i,j),rhs))))));
    }

    private static Formula WalkUpperFormula()
    {
        Formula v=X("V"),k=X("k"),r=X("R"),l=X("L"),m=X("m"),n=X("n"),i=X("i"),j=X("j");
        Formula he=ForIJ(k,Imp(EqF(Call("maskArc",m,i,j),X("true")),At(r,At(l,i),At(l,j))));
        return All("V",TypeT(),All("k",NatT(),All("R",Arr(v,Arr(v,X("Prop"))),All("L",Arr(FinT(k),v),All("m",NatT(),Imp(he,All("n",NatT(),ForIJ(k,Imp(EqF(Call("walkBound",m,n,i,j),X("true")),LeF(DD(r,At(l,i),At(l,j)),Cast(n,ENatT())))))))))));
    }

    private static Formula DimensionLowerFormula()
    {
        Formula v=X("V"),r=X("R"),k=X("k"),c=X("c"),s=X("S");
        Formula hb=All("S",Call("Finset",v),Imp(EqF(App(Q("Finset","card"),s),k),Imp(Solid(r,Cast(s,Call("Set",v))),LeF(Card(v),c))));
        return All("V",TypeT(),Seq(Inst("Fintype",v),All("R",Arr(v,Arr(v,X("Prop"))),All("k",NatT(),All("c",NatT(),Imp(LeF(k,Card(v)),Imp(LtF(c,Card(v)),Imp(hb,LeF(Add(k,N(1)),Call("solidMetricDimension",r))))))))));
    }


}
