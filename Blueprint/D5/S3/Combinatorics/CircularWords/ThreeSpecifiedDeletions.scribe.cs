using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class ThreeSpecifiedDeletionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three preselected distinct deletions reconstruct a nodup oriented circle on a fixed support of at least four labels; every prescribed pair fails.",
        H("Three Specified Circular Deletions"), Blocks(
            Paragraph(Text("Cycle identifies rotations and retains orientation. Fix a finite support A with at least four labels. "
                + "The observations are actual CircularDeletionTransport.delete outputs, indexed by their known deleted labels. "
                + "The labels a,b,c are chosen before observing either state. No reversal quotient, repeated labels, "
                + "unlabeled deck or adaptive choice is included.")),
            Describe.Lean(DescribeId.Create("three-specified"), DeclarationHandle.Create(Prefix + "reconstruct_three"),
                H("Any Three Specified Labels Suffice"), StatementSource.FromAuthor(ThreeFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Choose r in A outside {a,b,c}. Reuse DeletionReadoutReconstruction.rooted to represent both circles as r followed by a list. "
                    + "Since r survives each observation, CyclicInsertionGap.anchored_coe_injective turns equality of circular residuals "
                    + "into equality of the corresponding filtered tail lists. Three erasures distinguish arbitrary linear lists: "
                    + "induct on the first list, choose an erased label different from both current heads, identify the heads, "
                    + "then cancel any surviving common head in each of the three equalities and apply induction. "
                    + "This induction covers every finite length, including the empty tail, without enumeration. "
                    + "The private list lemma is consumed in this theorem. The original full-deck reconstruct theorem has a stronger "
                    + "observation hypothesis; its statement and proof remain the existing result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-insufficient"), DeclarationHandle.Create(Prefix + "two_deletions_insufficient"),
                H("Every Specified Pair Has a Collision"), StatementSource.FromAuthor(TwoFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any distinct a,b in A choose r outside {a,b}, and enumerate A minus {r,a,b} as a nodup list L. "
                    + "The actual circles r,a,b,L and r,b,a,L have exactly support A. Anchored uniqueness distinguishes them, "
                    + "while deletion of a gives r,b,L in both and deletion of b gives r,a,L in both. "
                    + "This direct pair-swap construction proves the observation-count boundary on an arbitrary common support. "
                    + "The existing three-label-support obstruction in DeletionReadoutReconstruction.deletion_joint_kernel_iff "
                    + "is independent background; this pair-collision proof does not use it."))), DescribeRole.Theorem),
            Paragraph(Text("The minimum-observation application uses the existing MinimumCompleteSetCover theorem without introducing a new budget framework. "
                + "Its state type X is SupportedCircle A, its observer index type is the subtype A, "
                + "its output family V(i) is Cycle T for each i in A, and q(i) is exactly deletionReadout A i. "
                + "A selected nonadaptive budget J is a Finset A; jointReadout restricts q to the subtype of labels belonging to J. "
                + "For every fixed support A of cardinality at least four, this selected joint readout is injective if and only if 3 <= J.card. "
                + "For sufficiency select three members of J and apply reconstruct_three. "
                + "If J has at most two members, enlarge it within A to a pair of distinct labels; "
                + "two_deletions_insufficient supplies distinct supported circles agreeing on that pair and hence on J. "
                + "This includes the empty and singleton budgets. The existing counterexample_certifies_incomplete_budget applies to that actual pair.")),
            Paragraph(Text("The existing finite_budget_injective_iff_cover identifies these complete deletion families with covers of all distinct ordered pairs of SupportedCircle A. "
                + "Under the natural unit cost c(i)=1, budgetCost J c equals J.card. "
                + "The existing minimum_complete_budget_iff_minimum_cover then says that IsMinimumCompleteBudget J (deletionReadout A) c "
                + "holds exactly when J.card=3: every complete competitor has at least three members, and A contains a complete triple. "
                + "All triples are therefore minimum, and every larger selected family is complete but has larger unit cost. "
                + "These are exact applications of existing results, so their binding-only checks remain transient rather than new named D5 declarations. "
                + "The cost counts exact deletion readouts of the same fixed object. A readout contains a whole residual circle of length |A|-1; "
                + "the result does not bound the number of encoded bits, the cost of accessing or copying the object, running time, adaptive strategies, or recovery from noise.")),
            Paragraph(Text("On X = SupportedCircle(A), the triple map J(C) = (delete(a,C),delete(b,C),delete(c,C)) is injective. "
                + "Direct application of Mathlib Finsupp.mapDomain_injective makes its pushforward injective on finitely supported signed masses "
                + "and hence on finite probability laws. This concerns the joint pushforward from one sample. "
                + "It does not identify the law from a family of individual marginal pushforwards, nor give a noise stability or sample complexity bound.")))));

    private static Formula ThreeFormula()
    {
        Formula a=F.Id("a"), b=F.Id("b"), c=F.Id("c"), A=F.Id("A"), C=F.Id("C"), Dd=F.Id("D");
        Formula distinct=And(Ne(a,b),And(Ne(a,c),Ne(b,c)));
        Formula obs=And(Eq(Call("delete",a,C),Call("delete",a,Dd)),And(Eq(Call("delete",b,C),Call("delete",b,Dd)),Eq(Call("delete",c,C),Call("delete",c,Dd))));
        Formula premise=And(Le(D(4),Call("card",A)),And(In(a,A),And(In(b,A),And(In(c,A),And(distinct,And(Supported(C,A),And(Supported(Dd,A),obs)))))));
        Formula quantified = All("A",Call("Finset",F.Id("T")),All("a",F.Id("T"),All("b",F.Id("T"),All("c",F.Id("T"),All("C",Call("Cycle",F.Id("T")),All("D",Call("Cycle",F.Id("T")),Imp(premise,Eq(C,Dd))))))));
        return Disp(All("T",Call("Type"),Seq(OpenBracket,Call("DecidableEq",F.Id("T")),CloseBracket,Sp,quantified)));
    }
    private static Formula TwoFormula()
    {
        Formula A=F.Id("A"),a=F.Id("a"),b=F.Id("b"),C=F.Id("C"),Dd=F.Id("D"),t=F.Id("T");
        Formula conclusion=And(Supported(C,A),And(Supported(Dd,A),And(Ne(C,Dd),And(Eq(Call("delete",a,C),Call("delete",a,Dd)),Eq(Call("delete",b,C),Call("delete",b,Dd))))));
        Formula quantified = All("A",Call("Finset",t),All("a",t,All("b",t,Imp(And(Le(D(4),Call("card",A)),And(In(a,A),And(In(b,A),Ne(a,b)))),Ex("C",Call("Cycle",t),Ex("D",Call("Cycle",t),conclusion))))));
        return Disp(All("T",Call("Type"),Seq(OpenBracket,Call("DecidableEq",t),CloseBracket,Sp,quantified)));
    }
    private static Formula Supported(Formula c,Formula a)=>And(Call("Nodup",c),Eq(Call("support",c),a));
    private static Formula Call(string name,params Formula[] args)=>args.Length==0?new Formula.NamedConstant(FormulaIdentifier.Create(name)):new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)),[..args]);
    private static Formula All(string n,Formula d,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Ex(string n,Formula d,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),d,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>new Formula.Not(Seq(Open,Eq(a,b),Close));
    private static Formula In(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(Seq(Open,a,Close),FormulaLogicOperator.And,Seq(Open,b,Close));
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(Seq(Open,a,Close),FormulaLogicOperator.Implies,Seq(Open,b,Close));
}
