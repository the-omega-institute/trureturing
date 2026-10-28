using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TotalDominationSeedsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual total-domination roots approach minus one from the right and are unbounded to the left.",
        H("Small-shift and unbounded total-domination roots"), Blocks(
            Paragraph(Text("A total dominating set S is an actual finite subset of the graph vertices. Every vertex v, including every selected vertex, must have a neighbour u in S. No independence, minimality, ordinary closed-neighbourhood domination, or connectedness restriction on S is substituted. The polynomial coefficients count exactly these subsets.")),
            Node("IsTotal", "Total domination", All("V",Type,All("G",Graph(V("V")),All("S",Set(V("V")),IffTo(Total(V("G"),V("S")),All("v",V("V"),Some("u",V("V"),And(Member(V("u"),V("S")),Adj(V("G"),V("v"),V("u"))))))))),
                "For every actual graph G : SimpleGraph V and S : Finset V, IsTotal G S is the displayed proposition. V is implicit and has universe Type. The relation is the existing symmetric, loopless SimpleGraph adjacency.", DescribeRole.Definition),
            Node("totalPolynomial", "The actual subset polynomial", SubsetPolynomial(false),
                "For every finite V with a Fintype instance and every SimpleGraph G on V, totalPolynomial G lies in the real polynomial ring. The displayed sum ranges over all S : Finset V of X raised to S.card when IsTotal G S holds, and zero otherwise. There is no supplied polynomial hypothesis.", DescribeRole.Definition),
            Node("unionGraph", "Disjoint union", BothTypes(All("G",Graph(V("V")),All("H",Graph(V("W")),And(All("v",V("V"),All("u",V("V"),IffTo(Adj(Call("unionGraph",V("G"),V("H")),Call("inl",V("v")),Call("inl",V("u"))),Adj(V("G"),V("v"),V("u"))))),All("a",V("W"),All("b",V("W"),IffTo(Adj(Call("unionGraph",V("G"),V("H")),Call("inr",V("a")),Call("inr",V("b"))),Adj(V("H"),V("a"),V("b"))))),All("v",V("V"),All("a",V("W"),IffTo(Adj(Call("unionGraph",V("G"),V("H")),Call("inl",V("v")),Call("inr",V("a"))),Call("False")))),All("a",V("W"),All("v",V("V"),IffTo(Adj(Call("unionGraph",V("G"),V("H")),Call("inr",V("a")),Call("inl",V("v"))),Call("False")))))))),
                "G : SimpleGraph V and H : SimpleGraph W give a graph on V sum W. Two left vertices use G adjacency, two right vertices use H adjacency, and vertices on opposite sides are not adjacent. The private subset equivalence union_total and sum bijection union_polynomial prove multiplicativity.", DescribeRole.Definition),
            Node("coneGraph", "A genuine universal vertex", All("V",Type,All("G",Graph(V("V")),And(All("a",Call("Unit"),All("b",Call("Unit"),IffTo(Adj(Call("coneGraph",V("G")),Call("inl",V("a")),Call("inl",V("b"))),Call("False")))),All("a",Call("Unit"),All("v",V("V"),IffTo(Adj(Call("coneGraph",V("G")),Call("inl",V("a")),Call("inr",V("v"))),Call("True")))),All("v",V("V"),All("a",Call("Unit"),IffTo(Adj(Call("coneGraph",V("G")),Call("inr",V("v")),Call("inl",V("a"))),Call("True")))),All("v",V("V"),All("u",V("V"),IffTo(Adj(Call("coneGraph",V("G")),Call("inr",V("v")),Call("inr",V("u"))),Adj(V("G"),V("v"),V("u")))))))),
                "The vertex type is Unit sum V. The sole left vertex is adjacent to every right vertex; two right vertices use G adjacency; no left-left adjacency is allowed. For nonempty finite V, splitting subsets by hub membership proves T_cone(x)=x((1+x)^card(V)-1)+T_G(x). The selected hub itself requires a selected old vertex, which explains the subtraction of one.", DescribeRole.Definition),
            Node("totalDecidable", "Decidability of actual total domination", All("V",Type,Inst(Call("Fintype",V("V")),All("G",Graph(V("V")),Inst(Call("DecidableRel",Call("Adj",V("G"))),All("S",Set(V("V")),Cast(Call("totalDecidable",V("G"),V("S")),Call("Decidable",Total(V("G"),V("S"))))))))),
                "The public instance has exactly the displayed dependent type. Unfolding IsTotal reduces it to finite decidable universal and existential quantification over adjacency and membership.", DescribeRole.Definition),
            Node("seedBaseFintype", "SeedBase finite enumeration", Instance("seedBaseFintype","SeedBase",false),
                "For every natural m this is the displayed instance. At zero use the canonical Fin instance; at a successor use instFintypeSum with the recursively supplied instance.", DescribeRole.Definition),
            Node("seedBaseNonempty", "SeedBase nonemptiness", Instance("seedBaseNonempty","SeedBase",true),
                "For every natural m this is the displayed instance. At zero the finite base contains zero; at a successor the left summand contains zero.", DescribeRole.Definition),
            Node("SeedBase", "The seed vertex types", RecursiveType("SeedBase",3),
                "m is any natural number. SeedBase 0 is Fin 3. SeedBase (m+1) is Fin 5 sum SeedBase m. Its exact cardinality is 5m+3. The explicit recursive Fintype instance supplies finite actual vertices at every unbounded order; the triangle supplies nonemptiness.", DescribeRole.Definition),
            Node("seedBaseGraph", "Five-cycles and a triangle", RecursiveGraph(true),
                "At m=0 this is the complete graph on Fin 3; at m+1 it is the disjoint union of the native cycleGraph 5 and seedBaseGraph m. Exact actual-subset enumeration gives T_C5=5x^3+5x^4+x^5 and T_K3=3x^2+x^3. Multiplicativity then gives their product for all m. These finite checks are consumed known ingredients of the unbounded seed estimate, not separate positive-instance results.", DescribeRole.Definition),
            Node("seedGraph", "The actual seed graph", All("m",Nat,Eq(Call("seedGraph",V("m")),Call("coneGraph",Call("seedBaseGraph",V("m"))))),
                "For every natural m, the result is a simple graph on Unit sum SeedBase m. It has 5m+4 vertices. The universal vertex and nonempty base give every vertex a neighbour.", DescribeRole.Definition),
            Node("seedPolynomial", "The explicit seed polynomial", All("m",Nat,Eq(Cast(Call("seedPolynomial",V("m")),PolynomialType(Real)),Add(Mul(V("X"),Sub(Pow(Add(D(1),V("X")),Add(Mul(D(5),V("m")),D(3))),D(1))),Mul(Pow(Add(Add(Mul(D(5),Pow(V("X"),D(3))),Mul(D(5),Pow(V("X"),D(4)))),Pow(V("X"),D(5))),V("m")),Add(Mul(D(3),Pow(V("X"),D(2))),Pow(V("X"),D(3))))))),
                "The defining expression is x((1+x)^(5m+3)-1)+(5x^3+5x^4+x^5)^m(3x^2+x^3) in R[X]. The private theorem seed_graph_polynomial identifies this expression with the actual subset totalPolynomial(seedGraph m); it is not an abstract replacement for that polynomial.", DescribeRole.Definition),
            Node("seed_root_right", "A root in every shrinking interval", SeedRoot(false),
                "For every natural s>=3 with Odd s, there is a real r strictly between -1 and -1+1/s at which seedPolynomial(s^2) vanishes. Write t=1/s, a=(1-t)^3(1+3t+t^2), and g=2-3t+t^3. The bounds 0<=a<=1-3t^2 and s^2*3t^2=3 imply a^(s^2)<=1/4 by Bernoulli, since a(1+3t^2)<=1. Also 0<=g<=2 and t^(5s^2+3)<=1/27. The hub term is at least 52/81 and the subtracted term at most 1/2, so the right endpoint value is positive. Oddness gives the left endpoint value -1. Continuity and the strict intermediate value theorem produce the root.", DescribeRole.Theorem),
            Node("actual_seed_root_right", "The same roots belong to genuine isolate-free graphs", SeedRoot(true),
                "The same s and interval witness r satisfy totalPolynomial(seedGraph(s^2)).IsRoot r, that actual polynomial is nonzero, and every actual vertex has a neighbour. Nonzeroness follows from its value -1 at -1. Thus selected vertices obey the total condition in a real graph; no zero polynomial or density hypothesis supplies the conclusion. The underlying graph has 5s^2+4 vertices. This theorem supplies the small shifted roots for the complex density argument. It does not prove roots dense in C: independent-fibre substitution, complex radial/angular approximation and final whole-plane assembly remain outside this statement.", DescribeRole.Theorem),
            Node("labelled_seed_root", "Exact finite labels", LabelledSeed(),
                "For every natural s>=3 with Odd s, there exist a natural n, an actual SimpleGraph G on Fin n, and a real r such that n=5s^2+4, n>=2, -1<r<-1+1/s, T_G(r)=0, T_G is nonzero, and for every vertex v there exists a neighbour u. The exact same graph and polynomial satisfy all clauses. The proof transports finite subsets through the inverse Fintype.equivFin equivalence and preserves adjacency and cardinality.", DescribeRole.Theorem),
            Node("arbitrarily_small_positive_shift", "Arbitrarily small positive shifted roots", SmallShift(false),
                "For every positive real epsilon there exist n, G : SimpleGraph (Fin n), and r : R with n>=2, 0<1+r<epsilon, T_G(r)=0, T_G nonzero, and every vertex having a neighbour. Choose k with 1/(k+1)<epsilon and the odd s=2k+3. Then 1/s<=1/(k+1), and labelled_seed_root supplies the witness. No order bound is imposed on n.", DescribeRole.Theorem),
            Node("complexPolynomial", "The literal complex-coefficient subset polynomial", SubsetPolynomial(true),
                "For every finite vertex type V and SimpleGraph G on V, complexPolynomial G is the sum over S : Finset V of the complex indeterminate X to S.card when IsTotal G S, and zero otherwise. It equals totalPolynomial G mapped by the real-to-complex ring homomorphism. Thus this is the same actual-subset counting definition in C[X].", DescribeRole.Definition),
            Node("WholePlaneDensity", "The unchanged full target", IffTo(Call("WholePlaneDensity"),Whole()),
                "The unchanged proposition, consumed by TotalDominationDensity.result, states: for every complex z and every positive real epsilon, there exist n : N, G : SimpleGraph (Fin n), and w : C such that n>=2, every vertex has a neighbour, complexPolynomial G is nonzero, w is a root of that same polynomial, and norm(w-z)<epsilon. Every selected vertex must have a selected neighbour, as encoded in IsTotal. This retains the original all-z/all-epsilon, unbounded-order question.", DescribeRole.Definition),
            Node("complex_seed_accumulation", "Complex roots accumulating at minus one", SmallShift(true),
                "For every positive real epsilon there exist n, G : SimpleGraph (Fin n), and r : R such that n>=2, every vertex has a neighbour, complexPolynomial G is nonzero, the complex cast of r is its root, 0<1+r, and norm((r:C)-(-1:C))<epsilon. The same actual graph supplies all clauses. This follows by the injective real-to-complex coefficient map from arbitrarily_small_positive_shift. It proves accumulation at one point and supplies the centre case of TotalDominationDensity.result.", DescribeRole.Theorem),
            Node("edgeBaseFintype", "EdgeBase finite enumeration", Instance("edgeBaseFintype","EdgeBase",false),
                "For every natural m this is the displayed instance. At zero use the canonical Fin instance; at a successor use instFintypeSum with the recursively supplied instance.", DescribeRole.Definition),
            Node("edgeBaseNonempty", "EdgeBase nonemptiness", Instance("edgeBaseNonempty","EdgeBase",true),
                "For every natural m this is the displayed instance. At zero the finite base contains zero; at a successor the left summand contains zero.", DescribeRole.Definition),
            Node("EdgeBase", "Disjoint-edge vertex types", RecursiveType("EdgeBase",2),
                "For every natural m, EdgeBase 0 is Fin 2 and EdgeBase (m+1) is Fin 2 sum EdgeBase m. It has exactly 2(m+1) actual vertices and explicit finite and nonempty instances.", DescribeRole.Definition),
            Node("edgeBaseGraph", "The actual disjoint matching", RecursiveGraph(false),
                "The base at zero is the complete graph on two vertices. Each successor takes the disjoint union with another complete two-vertex graph. Actual total domination selects both ends of every edge, so its actual subset polynomial is X^(2(m+1)). This known finite identity is consumed by the unbounded-root construction.", DescribeRole.Definition),
            Node("friendshipGraph", "The actual friendship graph", All("m",Nat,Eq(Call("friendshipGraph",V("m")),Call("coneGraph",Call("edgeBaseGraph",V("m"))))),
                "This is coneGraph(edgeBaseGraph m), on Unit sum EdgeBase m. All m+1 triangles share exactly the hub. The nonempty base and hub give a neighbour to every vertex, including the hub.", DescribeRole.Definition),
            Node("friendshipPolynomial", "The known friendship expression", All("m",Nat,Eq(Cast(Call("friendshipPolynomial",V("m")),PolynomialType(Real)),Add(Mul(V("X"),Sub(Pow(Add(D(1),V("X")),Mul(D(2),Add(V("m"),D(1)))),D(1))),Pow(V("X"),Mul(D(2),Add(V("m"),D(1))))))),
                "For every natural m this is X*((1+X)^(2(m+1))-1)+X^(2(m+1)) in R[X]. The private friendship_graph_polynomial proves literal equality with totalPolynomial(friendshipGraph m) by actual subset counting. Alikhani and Jafari, arXiv:1605.02222v1 Theorem 2.1(ii), give x(x+1)^(2n)+x^(2n)-x for n>=2. Our n=m+1 matches that range exactly when m>=1. The m=0 triangle base is proved locally by actual subset enumeration, giving 3X^2+X^3; it is not a literal attestation of that theorem beyond its range.", DescribeRole.Definition),
            Node("friendship_root_unbounded", "Actual total-domination roots are unbounded below", Friendship(false),
                "For every real R>2 there exist a natural m and a real r<-R such that r is a root of totalPolynomial(friendshipGraph m), that same actual polynomial is nonzero, and every vertex has a neighbour. Put a=(1-1/R)^2 in [0,1), and choose m with a^(m+1)<1/R using the pinned Archimedean power theorem. At -R the polynomial equals R^(2(m+1))*(1-R*a^(m+1))+R>0. At -Q, Q=2(m+1)+2, Bernoulli gives Q*(1-1/Q)^(2(m+1))>=2, making its value negative. The same Bernoulli inequality implies R<=Q. Strict IVT on [-Q,-R] supplies r. The positive endpoint value proves nonzeroness. This supplies an unbounded real seed family for the unchanged whole target; it asserts no arbitrary complex approximation.", DescribeRole.Theorem),
            Node("labelled_unbounded_negative_roots", "Unbounded roots with exact finite labels", Friendship(true),
                "For every real R>2 there exist n, G : SimpleGraph (Fin n), and r : R with n>=2, r<-R, every vertex having a neighbour, complexPolynomial G nonzero, and the complex cast of r a root of that same actual polynomial. The inverse Fintype.equivFin transports the friendship graph, its actual subsets, adjacency and cardinalities. The injective real-to-complex coefficient map preserves nonzeroness and roots. The graph has 2(m+1)+1 vertices for the m selected by friendship_root_unbounded.", DescribeRole.Theorem),
            Paragraph(Text("The friendship expression and total-domination definition are attested in Alikhani and Jafari. The cycle, triangle, cone and disjoint-union formulas are proved here from actual subsets and used as ingredients; these local proofs assert no original discovery of those identities. The complex target is the question of Shao and Zhao, section 5.2 Open Problem 2."))), []));

    private static AssessedProvenance Provenance(string selector) => selector is "IsTotal" or "totalPolynomial" or "complexPolynomial" or "friendshipPolynomial"
        ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Combinatorics/alikhani2016totalroots"))
        : selector == "WholePlaneDensity" ? AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Combinatorics/shao2026connectedroots"))
        : AssessedProvenance.FromRepo();
    private static DocumentBlock Node(string selector, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("td-seed-" + selector.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), Provenance(selector),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Type => Call("Type");
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Cast(Formula x, Formula t) => Par(Seq(x,Colon,t));
    private static Formula Pow(Formula x, Formula n) => Seq(Par(x),Caret,Grp(n));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.MemberOf,y);
    private static Formula And(params Formula[] xs) => xs.Length==1 ? xs[0] : new Formula.Logic(Par(xs[0]),FormulaLogicOperator.And,Par(And(xs[1..])));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x),FormulaLogicOperator.Implies,Par(y));
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(Par(x),FormulaLogicOperator.Iff,Par(y));
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Par(Seq(V(s),Colon,t)),Comma,Sp,b);
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists,Sp,Par(Seq(V(s),Colon,t)),Comma,Sp,b);
    private static Formula Inst(Formula t, Formula b) => Seq(OpenBracket,t,CloseBracket,Comma,Sp,b);
    private static Formula Graph(Formula t) => Call("SimpleGraph",t);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Set(Formula t) => Call("Finset",t);
    private static Formula SumType(Formula x, Formula y) => Call("Sum",x,y);
    private static Formula Adj(Formula g, Formula v, Formula u) => Call("Adj",g,v,u);
    private static Formula Total(Formula g, Formula s) => Call("IsTotal",g,s);
    private static Formula Poly(Formula g, bool complex=true) => Call(complex?"complexPolynomial":"totalPolynomial",g);
    private static Formula Root(Formula p, Formula w) => Call("IsRoot",p,w);
    private static Formula Norm(Formula x) => Seq(Vert,Sp,x,Vert);
    private static Formula NoIso(Formula g, Formula t) => All("v",t,Some("u",t,Adj(g,V("v"),V("u"))));
    private static Formula FiniteGraph(Formula b) => All("V",Type,Inst(Call("Fintype",V("V")),All("G",Graph(V("V")),b)));
    private static Formula BothTypes(Formula b, bool finite=false) => All("V",Type,All("W",Type,finite?Inst(Call("Fintype",V("V")),Inst(Call("Fintype",V("W")),b)):b));
    private static Formula PolynomialType(Formula t) => Seq(t,OpenBracket,V("X"),CloseBracket);
    private static Formula SubsetPolynomial(bool complex) => FiniteGraph(Eq(Poly(V("G"),complex),Seq(Sum,Underscore,Grp(Seq(V("S"),Colon,Set(V("V")))),Sp,Call("ite",Total(V("G"),V("S")),Pow(Cast(V("X"),PolynomialType(complex?Complex:Real)),Call("card",V("S"))),D(0)))));
    private static Formula Witness(Formula target) => Some("n",Nat,Some("G",Graph(Fin(V("n"))),Some("w",Complex,And(Leq(D(2),V("n")),NoIso(V("G"),Fin(V("n"))),Ne(Poly(V("G")),D(0)),Root(Poly(V("G")),V("w")),Lt(Norm(Sub(V("w"),target)),V("epsilon"))))));
    private static Formula Whole() => All("z",Complex,All("epsilon",Real,Imp(Lt(D(0),V("epsilon")),Witness(V("z")))));
    private static Formula SeedRoot(bool actual) {
        var s=V("s");var r=V("r");var g=Call("seedGraph",Pow(s,D(2)));var p=actual?Poly(g,false):Call("seedPolynomial",Pow(s,D(2)));
        var b=And(Lt(Seq(Minus,D(1)),r),Lt(r,Add(Seq(Minus,D(1)),new Formula.Fraction(D(1),Cast(s,Real)))),Root(p,r));
        if(actual)b=And(Lt(Seq(Minus,D(1)),r),Lt(r,Add(Seq(Minus,D(1)),new Formula.Fraction(D(1),Cast(s,Real)))),Root(p,r),Ne(p,D(0)),NoIso(g,SumType(Call("Unit"),Call("SeedBase",Pow(s,D(2))))));
        return All("s",Nat,Imp(Leq(D(3),s),Imp(Call("Odd",s),Some("r",Real,b))));
    }
    private static Formula LabelledSeed() => All("s",Nat,Imp(Leq(D(3),V("s")),Imp(Call("Odd",V("s")),Some("n",Nat,Some("G",Graph(Fin(V("n"))),Some("r",Real,And(Eq(V("n"),Add(Mul(D(5),Pow(V("s"),D(2))),D(4))),Leq(D(2),V("n")),Lt(Seq(Minus,D(1)),V("r")),Lt(V("r"),Add(Seq(Minus,D(1)),new Formula.Fraction(D(1),Cast(V("s"),Real)))),Root(Poly(V("G"),false),V("r")),Ne(Poly(V("G"),false),D(0)),NoIso(V("G"),Fin(V("n"))))))))));
    private static Formula SmallShift(bool complex) {
        var g=V("G");var r=V("r");var shift=Add(D(1),r);
        var body=complex?And(Leq(D(2),V("n")),NoIso(g,Fin(V("n"))),Ne(Poly(g),D(0)),Root(Poly(g),Cast(r,Complex)),Lt(D(0),shift),Lt(Norm(Sub(Cast(r,Complex),Cast(Seq(Minus,D(1)),Complex))),V("epsilon"))):And(Leq(D(2),V("n")),Lt(D(0),shift),Lt(shift,V("epsilon")),Root(Poly(g,false),r),Ne(Poly(g,false),D(0)),NoIso(g,Fin(V("n"))));
        return All("epsilon",Real,Imp(Lt(D(0),V("epsilon")),Some("n",Nat,Some("G",Graph(Fin(V("n"))),Some("r",Real,body)))));
    }
    private static Formula RecursiveType(string s, byte size) => And(Eq(Call(s,D(0)),Fin(D(size))),All("m",Nat,Eq(Call(s,Add(V("m"),D(1))),SumType(Fin(D(s=="SeedBase"?(byte)5:(byte)2)),Call(s,V("m"))))));
    private static Formula RecursiveGraph(bool seed) => And(Eq(Call(seed?"seedBaseGraph":"edgeBaseGraph",D(0)),Cast(Call("top"),Graph(Fin(D(seed?(byte)3:(byte)2))))),All("m",Nat,Eq(Call(seed?"seedBaseGraph":"edgeBaseGraph",Add(V("m"),D(1))),Call("unionGraph",seed?Call("cycleGraph",D(5)):Cast(Call("top"),Graph(Fin(D(2)))),Call(seed?"seedBaseGraph":"edgeBaseGraph",V("m"))))));
    private static Formula Instance(string s, string baseName, bool nonempty) => All("m",Nat,Cast(Call(s,V("m")),Call(nonempty?"Nonempty":"Fintype",Call(baseName,V("m")))));
    private static Formula Friendship(bool labelled) {
        var r=V("r");var g=labelled?V("G"):Call("friendshipGraph",V("m"));var t=labelled?Fin(V("n")):SumType(Call("Unit"),Call("EdgeBase",V("m")));
        var body=labelled?And(Leq(D(2),V("n")),Lt(r,Seq(Minus,V("R"))),NoIso(g,t),Ne(Poly(g),D(0)),Root(Poly(g),Cast(r,Complex))):And(Lt(r,Seq(Minus,V("R"))),Root(Poly(g,false),r),Ne(Poly(g,false),D(0)),NoIso(g,t));
        var ex=labelled?Some("n",Nat,Some("G",Graph(t),Some("r",Real,body))):Some("m",Nat,Some("r",Real,body));
        return All("R",Real,Imp(Lt(D(2),V("R")),ex));
    }
}
