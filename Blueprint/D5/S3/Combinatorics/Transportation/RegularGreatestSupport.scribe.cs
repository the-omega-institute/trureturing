using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class RegularGreatestSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef AK =
        LibraryNoteRef.Create("D5/L/Semigroups/atserias2025witnesses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint additive observations over conical regular commutative coefficients admit a witness of greatest support on every finite coordinate carrier.",
        H("Greatest support for regular coefficients"),
        Blocks(Describe.Lean(
            DescribeId.Create("regular-greatest-joint-support"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/RegularGreatestSupport.result"),
            H("Greatest support in every nonempty observation fiber"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(AK),
            Blocks(
                Paragraph(Text("K is an arbitrary commutative additive monoid. Conicality C(K) means that x+y=0 implies x=y=0. Regularity R(K) means that for every x there is y with x+y+x=x. The coordinate type I is finite, including the empty type. J is arbitrary in its own universe. M is a dependent family of types in another universe, with an AddMonoid instance for each M(j). Each F(j) is an additive monoid homomorphism from the original pointwise additive monoid I→K to M(j). There is no commutativity or regularity premise on the targets. E(q,p) abbreviates equality F(j)(q)=F(j)(p) for every j, and S(q,r) abbreviates q(i)≠0 implies r(i)≠0 for every i.")),
                Paragraph(Text("The supplied vector p makes the fiber nonempty. The result returns a feasible vector r whose support contains the support of every feasible q. It asserts neither uniqueness of annotations nor a greatest annotation in any order. All additions, zeros, homomorphisms and equalities remain those of the original monoids. There is no finite K, nonempty I, nonempty J, nontriviality, multiplication, cancellation, divisibility, order, refinement or purity premise.")),
                Paragraph(Text("The reusable construction is in Omega.Refinement.Regular.joint_fiber_support_union and exists_greatest_joint_fiber_support. For each coordinate of q choose its component idempotent e, using regular_component_idempotent from the regular-component library. The existing component_identity gives q+e=q. Mutual algebraic-preorder membership and conicality give e(i)=0 exactly when q(i)=0: each implication uses an additive difference whose sum is zero. Thus r=p+e has support exactly supp(p)∪supp(q). For each j, additivity and equal observations give F(j)(p+e)=F(j)(p)+F(j)(e)=F(j)(q)+F(j)(e)=F(j)(q+e)=F(j)(p). This calculation needs no cancellation or commutation in M(j). The binary construction itself does not require finite I.")),
                Paragraph(Text("The supports of feasible vectors are therefore a directed family under inclusion. For each coordinate that can be nonzero, choose one feasible vector attaining it; for other coordinates use p. This gives a finite family. Mathlib's Directed.finset_le supplies a feasible upper bound for its supports, which contains every attainable coordinate. If I is empty the selected family is empty and the original feasible p supplies nonemptiness of the directed family. No enumeration of coefficient values or observations is used.")),
                Paragraph(Text("For the annotated-relation application of Atserias and Kolaitis, let R(X) and S(Y) be two consistent finitely supported K-relations and choose one existing consistency witness P(X∪Y). Let T be the ordinary relational join of supp(R) and supp(S). This is a finite joint-tuple carrier: restriction to X and Y embeds it in the product of the two finite marginal supports. Positivity implies that every consistency witness Q has support contained in T. Indeed, a nonzero annotation at t is a summand of each projected marginal at t|X and t|Y; a zero marginal sum would force that summand to be zero. This uses each Q's finite support, as required by the definition of a K-relation.")),
                Paragraph(Text("Restrict annotations to T and put p=P|T. The X-marginal observation sends a vector a:T→K to the function x↦∑{t∈T:t|X=x}a(t), and the Y-marginal is defined in the same way. Their targets are function monoids with pointwise addition. Finite sums preserve zero and addition, so both observations are additive monoid homomorphisms. The equations F_X(a)=R and F_Y(a)=S are exactly the joint observation fiber of p. The theorem gives r:T→K in that fiber containing every restricted feasible support. Extending r by zero outside T gives a finitely supported consistency witness whose support contains the support of every Q, because coordinate nonzero is precisely relational support. Empty supports and empty tuple carriers are included.")),
                Paragraph(Text("This is a sufficient coefficient class for the largest-consistency-witness question in AK25 Section 8, pages 15–17. Feasibility comes from the specified existing witness p. Equality on overlapping marginals alone is not asserted to produce a witness. The complete coefficient classification remains unresolved by this theorem; the separate transportation criterion requires additional hypotheses and is not used here.")),
                Paragraph(Text("The coefficient class preserves internal group information. Given any abelian group G, adjoin a distinct global additive zero to its underlying additive semigroup. Two embedded group elements add using G; the new zero is an identity. This monoid is conical and regular: embedded g has internal inverse −g and local identity the embedded group zero. For a nontrivial G it is not idempotent, and for infinite G the coefficient monoid is infinite. Neither the local identity nor internal cancellation is identified with the new global zero. This description is an ordinary mathematical model; the generic Lean theorem does not require an instance of it.")),
                Paragraph(Text("A second use is any finite system of additive measurements of a coefficient vector: fixing all measured values to those of an existing p leaves a solution activating every coordinate that any solution can activate. The number of measurements may be infinite, and their target monoids may differ. The conclusion concerns exact feasibility and support containment, with no algorithmic running-time or weight-maximization assertion."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Some(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula t, Formula b) => Seq(OpenBracket, Call(n,t), CloseBracket, Comma, Sp, b);

    private static Formula Statement()
    {
        Formula k=V("K"), i=V("I"), j=V("J"), p=V("p"), q=V("q"), r=V("r");
        Formula vectors=Arrow(i,k);
        Formula conclusion=Some("r",vectors,And(Call("E",r,p),All("q",vectors,Imp(Call("E",q,p),Call("S",q,r)))));
        Formula homs=All("j",j,Call("AddMonoidHom",vectors,Call("M",V("j"))));
        Formula targetInstances=All("j",j,Call("AddMonoid",Call("M",V("j"))));
        Formula statement=All("p",vectors,conclusion);
        statement=All("F",homs,statement);
        statement=Seq(OpenBracket,targetInstances,CloseBracket,Comma,Sp,statement);
        statement=All("M",Arrow(j,V("Type")),statement);
        statement=All("J",V("Type"),statement);
        statement=All("I",V("Type"),Inst("Finite",i,statement));
        statement=Imp(Call("C",k),Imp(Call("R",k),statement));
        return All("K",V("Type"),Inst("AddCommMonoid",k,statement));
    }
}
