using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class AbsorptionGreatestSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef AK =
        LibraryNoteRef.Create("D5/L/Semigroups/atserias2025witnesses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero absorption exactly characterizes universal greatest support for finite additive-observation fibers over conical commutative coefficients.",
        H("Absorption and universal greatest support"),
        Blocks(Describe.Lean(
            DescribeId.Create("absorption-iff-universal-greatest-support"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/AbsorptionGreatestSupport.result"),
            H("The exact original-coefficient equivalence"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(AK),
            Blocks(
                Paragraph(Text("Fix any universe u and any K:Type u with its original AddCommMonoid structure. Conicality means x+y=0 implies x=0 and y=0. The left side A says that each nonzero x absorbs some nonzero e: x+e=x. The right side H quantifies over every natural number n, every T:Type u with an AddMonoid instance, every additive monoid homomorphism F:(Fin n→K)→+T, and every p. It returns r with F(r)=F(p) and, for every q with F(q)=F(p), every coordinate nonzero in q is nonzero in r. The zero, addition and equality in every clause are the original ones. In the displayed formula, Nat denotes ℕ and Typeu denotes Type u. The displayed add denotes this addition; applications p(i), F(p) have their usual meanings.")),
                Paragraph(Text("Empty powers n=0 and trivial coefficient monoids are included. There is no regularity, refinement, order, cancellation, division, idempotency, finite-coefficient or nontriviality premise. Targets need not be commutative. The conclusion is a greatest support, with no assertion of a greatest coefficient vector, uniqueness, an algorithm, or a running-time bound. The target universe is part of H: the reverse proof uses a quotient of Fin 2→K, and makes no converse assertion for a smaller target universe unable to contain that observer.")),
                Paragraph(Text("For A⇒H, choose e(i)=0 when q(i)=0, and otherwise choose a nonzero e(i) with q(i)+e(i)=q(i). Thus q+e=q and e has exactly q's support. Given F(p)=F(q), additivity gives F(p+e)=F(p)+F(e)=F(q)+F(e)=F(q+e)=F(p). Conicality gives supp(p+e)=supp(p)∪supp(q). This is the reusable fiber_support_union theorem, which allows arbitrary coordinate and target universes and does not require finite coordinates. In a finite power choose one feasible witness for each coordinate that can be nonzero. Feasible supports are directed by the binary union construction, so Directed.finset_le bounds this finite selected family by a feasible support. The original p supplies nonemptiness even when the coordinate set is empty.")),
                Paragraph(Text("For H⇒A, suppose x≠0 and x+e=x forces e=0. In K² let p=(x,0), q=(0,x), and S={p,q}. For every vector c, p+c∈S iff c=0, and q+c∈S iff c=0. In the equal-singleton case this follows from the assumed trivial absorption stabilizer; in the opposite-singleton case conicality would force x=0. Define the additive congruence a∼b iff, for every c, a+c∈S iff b+c∈S. Associativity and commutativity make this relation compatible with addition. It identifies p and q. For its quotient homomorphism F, any r with F(r)=F(p) belongs to S, by taking context c=0. But a greatest-support r must be nonzero in both coordinates because p and q are feasible. Neither member of S has that support, a contradiction. This is a universal-observer obstruction in the original coefficient monoid, with a quotient target in Type u.")),
                Paragraph(Text("For the annotated-relation application in Atserias and Kolaitis, Section 8, pages 15–17, begin with two finitely supported K-relations R(X), S(Y) and an existing consistency witness P. Let C be the finite ordinary join of the two marginal supports. Restriction to X and Y embeds C into the product of the two finite supports. Every consistency witness Q has support contained in C: a nonzero annotation contributes to each marginal sum, and conicality forces every summand of a zero finite sum to be zero. This uses the finite support required in the definition of each K-relation.")),
                Paragraph(Text("Restrict P to C and enumerate C by Fin n. Enumerate the finite marginal supports of R and S by Fin r and Fin s, respectively, allowing r=0 or s=0. Each marginal map is an additive homomorphism: its value at an indexed marginal tuple is the finite sum of annotations over the corresponding restriction fiber. Their product is one additive observer F:(Fin n→K)→+((Fin r→K)×(Fin s→K)). Its target (Fin r→K)×(Fin s→K) lies in Type u because Fin r and Fin s lie in Type 0 and K:Type u, irrespective of the ambient tuple universes. The finite-join restriction makes projected values outside the marginal supports zero, as in the preceding conicality argument, so this observer records exactly the required full marginals. Its fiber at P is exactly the set of restricted consistency witnesses. Apply A⇒H and extend the returned vector by zero outside C. This gives a finitely supported consistency witness containing the support of every Q. Feasibility is supplied by P; agreement of overlapping marginals alone is not asserted to produce P. This extends the sufficient coefficient hypothesis from regularity to A. Conversely, the quotient observer in H⇒A is an arbitrary additive observer, with no proof that it is a marginal map. The universal all-observer classification therefore does not settle the full marginal coefficient classification in AK25.")),
                Paragraph(Text("A includes conical nonregular coefficients. Take K=WithZero ℕ with the additive structure obtained by adjoining a new additive zero to the additive semigroup ℕ. Its elements are a new zero and symbols [n], with [m]+[n]=[m+n]; the new zero is an identity. It is conical. Every nonzero [n] absorbs the nonzero internal identity [0]. But [1]+y+[1]=[1] has no solution: y equal to the new zero gives [2]=[1], and y=[m] gives 2+m=1. This same original additive structure satisfies A and H and fails regularity. Thus the sufficient class is strictly larger than the conical regular class; this statement does not assert necessity for marginal observers.")),
                Paragraph(Text("A second application is a finite vector of original coefficients subject to arbitrary additive measurements. If one feasible vector is known and the coefficient monoid satisfies conicality and A, a feasible vector activates every coordinate attainable by any feasible vector. Several same-universe measurements combine into a product observer. The construction proves exact support feasibility and makes no optimization or complexity claim. The new equivalence is a repository synthesis; AK25 supplies the marginal problem and application context, rather than this universal equivalence. The pinned congruence and finite-directedness APIs supply infrastructure, rather than the absorption characterization."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Some(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula t, Formula b) => Seq(OpenBracket, Call(n,t), CloseBracket, Comma, Sp, b);

    private static Formula Statement()
    {
        Formula k=V("K"), x=V("x"), y=V("y"), e=V("e"), z=D(0);
        Formula n=V("n"), t=V("T"), p=V("p"), q=V("q"), r=V("r"), i=V("i");
        Formula vectors=Arrow(Call("Fin",n),k);
        Formula conical=All("x",k,All("y",k,Imp(Eq(Call("add",x,y),z),And(Eq(x,z),Eq(y,z)))));
        Formula absorption=All("x",k,Imp(Ne(x,z),Some("e",k,And(Ne(e,z),Eq(Call("add",x,e),x)))));
        Formula support=All("i",Call("Fin",n),Imp(Ne(new Formula.Apply(q,[i]),z),Ne(new Formula.Apply(r,[i]),z)));
        Formula feasibleQ=Eq(Call("F",q),Call("F",p));
        Formula greatest=Some("r",vectors,And(Eq(Call("F",r),Call("F",p)),All("q",vectors,Imp(feasibleQ,support))));
        Formula universal=All("n",V("Nat"),All("T",V("Typeu"),Inst("AddMonoid",t,
            All("F",Call("AddMonoidHom",vectors,t),All("p",vectors,greatest)))));
        Formula equivalence=new Formula.Logic(absorption,FormulaLogicOperator.Iff,universal);
        return All("K",V("Typeu"),Inst("AddCommMonoid",k,Imp(conical,equivalence)));
    }
}
