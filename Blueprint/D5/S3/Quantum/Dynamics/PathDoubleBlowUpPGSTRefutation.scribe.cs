using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PathDoubleBlowUpPGSTRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/bhattacharjyamonterdepal2024blowup");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The double blow-up of P_11 admits pretty good state transfer between the two copies of source vertex 4, refuting Conjecture 1 of Bhattacharjya, Monterde and Pal.",
        H("Pretty good state transfer at vertex 4 of the double blow-up of P_11"), Blocks(
            Node("pathAdj", "Path adjacency", PathFormula(),
                "Source vertices are 1 through n. A vertex j in Fin(n) represents source vertex val(j) + 1, so adjacency is the disjunction val(i) + 1 = val(j) or val(j) + 1 = val(i). Matrix entries are complex zero and one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("doubleBlowUp", "The double blow-up", BlowFormula(),
                "Section 2, page 2 states: The blow-up of G, denoted by ⊎ⁿG, is the graph with vertex set ℤ_n × V, and two vertices (l, u) and (m, v) are adjacent in ⊎ⁿG if and only if the vertices u and v are adjacent in G. Here the number of copies is two, with carrier Fin(2) times Fin(n). The copy coordinates do not affect adjacency.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("PGST", "Pretty good state transfer", PGSTFormula(),
                "Section 1, pages 1-2 states: A graph G exhibits PGST between u and v if there is a sequence τ_k ∈ ℝ such that lim_{k→∞} |U(τ_k)_{u,v}| = 1, i.e., |U(t)_{u,v}|² can be made arbitrarily close to one through appropriate choices of t. The matrix U(t) is exp(itA), represented by hamiltonianPropagator(A, -t). The sequence is indexed by the naturals and convergence is Tendsto atTop to nhds(1). Complex modulus is the Lean norm.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Section 8, page 8, Conjecture 1 states: Let n = 2^t r − 1, where t ≥ 2 and r is an odd prime number. If u is a multiple of 2^{t−1}, then PGST does not occur between (0, u) and (1, u) in the double blow-up of P_n. The letters t and r retain their source meaning. The source vertex u is represented by u in Fin(2^t*r - 1), whose one-based label is val(u) + 1. Both subtractions in the displayed formula are Nat.sub, the truncated natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation by source vertex 4 of P_11", Disp(new Formula.Not(F.Id("claim"))),
                "Take t = 2, r = 3 and u = 3 in Fin(11), representing source vertex 4. At that vertex the diagonal amplitude is one quarter of the sum of the four cosines with positive frequencies (sqrt(6)+sqrt(2))/2, sqrt(3), 1 and (sqrt(6)-sqrt(2))/2. Each pair of opposite eigenvalues carries weight one eighth on each eigenvalue. Biquadratic independence and the finite-torus character criterion give times pi/2 + pi*m(k) along which all four cosines tend to minus one. The general twin-amplitude identity then gives modulus tending to one. The source's relation theta_5 - theta_9 + theta_11 = 0 uses theta_9 = -sqrt(2); this eigenvalue has zero weight at source vertex 4, since sin(3*pi) = 0, and therefore does not obstruct transfer there.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bmp-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula All(string v, Formula ty, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), ty, body);
    private static Formula Some(string v, Formula ty, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), ty, body);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula App(Formula x, params Formula[] args) => new Formula.Apply(x, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        App(Qualified(owner, name), args);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula x, Formula ty) => Parenthesized(Seq(x, Colon, ty));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Inst(string cls, Formula ty) => Seq(OpenBracket, Call(cls, ty), CloseBracket, Sp);
    private static Formula MatrixOf(Formula i) => Call("Matrix", i, i, C);
    private static Formula Propagator(Formula a, Formula t, Formula u, Formula v) =>
        App(QCall("ProjectionProbabilityFlow", "hamiltonianPropagator", a, t), u, v);
    private static Formula Lambda(string v, Formula ty, Formula body) =>
        Parenthesized(Seq(F.Id(v), Colon, ty, Sp, Mapsto, Sp, body));
    private static Formula Limit(Formula f, Formula z) =>
        Call("Tendsto", f, F.Id("atTop"), Call("nhds", z));

    private static Formula PathFormula()
    {
        Formula n=F.Id("n"), i=F.Id("i"), j=F.Id("j");
        Formula adjacent=Or(Equal(Add(Call("val",i),D(1)),Call("val",j)),
            Equal(Add(Call("val",j),D(1)),Call("val",i)));
        Formula ite=Seq(F.Text,Grp(F.Id("if")),Sp,Parenthesized(adjacent),Sp,
            F.Text,Grp(F.Id("then")),Sp,Cast(D(1),C),Sp,F.Text,Grp(F.Id("else")),Sp,Cast(D(0),C));
        return Disp(All("n",N,All("i",FinOf(n),All("j",FinOf(n),
            Equal(App(Call("pathAdj",n),i,j),ite)))));
    }
    private static Formula BlowFormula()
    {
        Formula n=F.Id("n"), p=F.Id("p"), q=F.Id("q");
        Formula carrier=Seq(FinOf(D(2)),Sp,Times,Sp,FinOf(n));
        Formula second(Formula a) => Seq(a,Dot,D(2));
        return Disp(All("n",N,All("p",carrier,All("q",carrier,
            Equal(App(Call("doubleBlowUp",n),p,q),App(Call("pathAdj",n),second(p),second(q)))))));
    }
    private static Formula PGSTFormula()
    {
        Formula i=F.Id("I"), a=F.Id("A"), u=F.Id("a"), v=F.Id("b");
        Formula seq=Lambda("k",N,Seq(Vert,Sp,Propagator(a,Negate(App(F.Id("s"),F.Id("k"))),u,v),Vert));
        Formula property=Some("s",Arrow(N,R),Limit(seq,D(1)));
        return Disp(All("I",F.Id("Type"),Seq(Inst("Fintype",i),Inst("DecidableEq",i),
            All("A",MatrixOf(i),All("a",i,All("b",i,Iff(Call("PGST",a,u,v),property)))))));
    }
    private static Formula ClaimFormula()
    {
        Formula t=F.Id("t"), r=F.Id("r"), u=F.Id("u");
        Formula n=QCall("Nat","sub",Mul(Pow(D(2),t),r),D(1));
        Formula divides=new Formula.Relation(Pow(D(2),QCall("Nat","sub",t,D(1))),
            FormulaRelationOperator.Divides,Add(Call("val",u),D(1)));
        Formula body=All("t",N,All("r",N,Implies(Le(D(2),t),
            Implies(QCall("Nat","Prime",r),Implies(Call("Odd",r),All("u",FinOf(n),
                Implies(divides,new Formula.Not(Call("PGST",Call("doubleBlowUp",n),Pair(D(0),u),Pair(D(1),u))))))))));
        return Disp(Iff(F.Id("claim"),body));
    }
}
