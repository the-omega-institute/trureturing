using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class GroupGreatestSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef AK =
        LibraryNoteRef.Create("D5/L/Semigroups/atserias2025witnesses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An abelian group admits greatest support in every finite additive-observation fiber exactly when it is torsion-free.",
        H("Group coefficients and greatest support"),
        Blocks(Describe.Lean(
            DescribeId.Create("group-torsion-free-iff-greatest-support"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/GroupGreatestSupport.result"),
            H("Torsion-freeness characterizes the universal support event"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(AK),
            Blocks(
                Paragraph(Text("Fix an arbitrary universe u and a type G:Type u equipped with its original AddCommGroup structure. Torsion-freeness means that for every positive natural k and every x:G, k times x equal to zero implies x equal to zero. Here times denotes repeated addition, written nsmul in the displayed formula. Nat denotes the natural numbers and Typeu denotes Type u. The right side quantifies over every natural n, every T:Type u with an AddMonoid structure, every additive monoid homomorphism F:(Fin n→G)→+T, and every feasible base vector p. It returns r with F(r)=F(p) such that every coordinate nonzero in any q satisfying F(q)=F(p) is nonzero in r. All zeros, additions, natural scalar multiples and equalities are the original ones.")),
                Paragraph(Text("The empty power n=0 and the trivial group are included. There is no order, conicality, finite generation, divisibility, field structure, finite coefficient carrier, nontriviality, target commutativity or target group premise. The conclusion concerns support containment, without asserting uniqueness, coefficient maximality or a computational bound. In particular, a target need not support subtraction. The target universe is part of the statement: the converse uses a quotient of a finite power of G, which lies in Type u.")),
                Paragraph(Text("For the forward implication, consider p and q with equal observations and put d=q−p. The kernel of an additive homomorphism from a group to an additive monoid is an additive subgroup. Thus d lies in the kernel, and p+m times d has the same observation as p for every natural m. This argument uses AddMonoidHom.sub_mem_ker_iff, subgroup closure under natural scalar multiples and additivity; it performs no cancellation in T.")),
                Paragraph(Text("For a fixed coordinate i, if d(i) is nonzero, torsion-freeness makes m↦m times d(i) injective on the natural numbers. Indeed, equality at m and n makes the integer multiple (m−n) times d(i) zero; the positive-natural torsion condition, applied also to negative integer multiples by negation, forces m=n. Hence p(i)+m times d(i)=0 excludes at most one m. If d(i)=0 and at least one of p(i),q(i) is nonzero, that coordinate never vanishes along the line. The union of these exceptional sets over finitely many coordinates is finite. Choose a natural m outside it. The resulting feasible r retains every coordinate in the union of the supports of p and q. This is exists_line_support_union followed by fiber_support_union in Omega.Refinement.GroupSupport.")),
                Paragraph(Text("Feasible supports are consequently directed under inclusion. Choose one feasible vector for each coordinate that can be nonzero, and use p where no such vector exists. This is a finite family, so Directed.finset_le supplies a feasible support containing all of them. Every feasible support is contained in that support. The reusable exists_greatest_fiber_support permits any finite coordinate type and any target universe. The given p supplies nonemptiness even when the coordinate type is empty.")),
                Paragraph(Text("For the converse, suppose that k is positive, k times x=0 and x is nonzero. On Fin k→G let d be the constant vector x and let K be the cyclic additive subgroup of all integer multiples of d. Use the quotient homomorphism F to (Fin k→G)/K and the vector p(i)=−i times x. Both p and p+d are in the fiber. At each coordinate either p(i) is already nonzero or p(i)=0 and (p+d)(i)=x is nonzero. A greatest-support vector r in this fiber must therefore be nonzero everywhere.")),
                Paragraph(Text("On the other hand, equality of quotient observations gives r−p=z times d for some integer z. Choose i in Fin k whose value is the nonnegative residue of z modulo k. Since k times x=0, Euclidean division gives i times x=z times x. The i-th coordinate equation is then r(i)+i times x=i times x, so r(i)=0, a contradiction. No minimality of k or assumption on other elements of G is used. The obstruction is a quotient of the whole ambient finite power, not an observation restricted to the torsion subgroup. The residue_smul calculation is the integer Euclidean-division bridge used by torsion_free_of_universal_greatest_support.")),
                Paragraph(Text("The displayed equivalence is exactly the result declaration. Its left side is TorsionFree G and its right side is UniversalGreatestSupport G after unfolding their definitions; torsion_free_iff_universal_greatest_support combines the two constructions. The quotient target is a permissible additive group instance of an arbitrary additive-monoid target. The forward proof holds for all permitted targets, and the reverse needs only this particular permitted observation. Finite k, including k=1, and arbitrary n are treated by the same formulas.")),
                Paragraph(Text("Atserias and Kolaitis, Section 8, pages 15–17, ask for positive commutative coefficient monoids admitting largest marginal witnesses. A nontrivial abelian group is outside that positive coefficient setting: a nonzero x and its inverse sum to the original zero. This equivalence instead classifies abelian group coefficients for all finite additive observations. Without positivity there is no claim that fixed marginal supports confine all feasible annotations to their finite ordinary join. Thus the result gives the exact group boundary for the universal observation event and does not resolve the positive-monoid marginal classification. The characterization here is a mathematical synthesis; no literature-priority claim is made."))),
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
        Formula g=V("G"), k=V("k"), x=V("x"), z=D(0);
        Formula n=V("n"), t=V("T"), p=V("p"), q=V("q"), r=V("r"), i=V("i");
        Formula vectors=Arrow(Call("Fin",n),g);
        Formula positive=new Formula.Relation(z,FormulaRelationOperator.LessThan,k);
        Formula tf=All("k",V("Nat"),Imp(positive,All("x",g,Imp(Eq(Call("nsmul",k,x),z),Eq(x,z)))));
        Formula support=All("i",Call("Fin",n),Imp(Ne(new Formula.Apply(q,[i]),z),Ne(new Formula.Apply(r,[i]),z)));
        Formula feasibleQ=Eq(Call("F",q),Call("F",p));
        Formula greatest=Some("r",vectors,And(Eq(Call("F",r),Call("F",p)),All("q",vectors,Imp(feasibleQ,support))));
        Formula universal=All("n",V("Nat"),All("T",V("Typeu"),Inst("AddMonoid",t,
            All("F",Call("AddMonoidHom",vectors,t),All("p",vectors,greatest)))));
        Formula equivalence=new Formula.Logic(tf,FormulaLogicOperator.Iff,universal);
        return All("G",V("Typeu"),Inst("AddCommGroup",g,equivalence));
    }
}
