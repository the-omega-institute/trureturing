using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class FourCycleMarginalCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/CircularWords/FourCycleMarginalCollision.";
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Individual circular-deletion marginals fail to determine a finite probability law, while paired readings from the same sample distinguish the exhibited laws.",
        H("Marginals and Paired Circular Readings"),Blocks(
            Paragraph(Text("Take actual Cycle(Nat) states X1=0123, X2=0321, Y1=0132, Y2=0231 modulo rotation, retaining orientation. "
                + "Let mu assign one half to each X state, and nu assign one half to each Y state, with all other masses zero. "
                + "Use rational Finsupp masses. J02(C)=(delete(0,C),delete(2,C)) records two observations from the same sample. "
                + "pairedEvent is the indicator of {J02(X1),J02(X2)}.")),
            Describe.Lean(DescribeId.Create("actual-marginal-collision"),DeclarationHandle.Create(Prefix+"actual_marginal_collision"),
                H("Equal Four Marginals and Disjoint Laws"),StatementSource.FromAuthor(Statement()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both supports consist of nodup circles with support {0,1,2,3}. Both masses are nonnegative and normalized, "
                    + "and the supports are disjoint. For deletion labels 0,1,2,3, the residual pairs of X states respectively are "
                    + "(123,132), (023,032), (013,031), (012,021), using canonical rotations. The Y states give respectively "
                    + "(132,123), (032,023), (013,031), (012,021). Hence all four pushforward marginals agree. "
                    + "The paired readings are X1:(123,013), X2:(132,031), Y1:(132,013), Y2:(123,031). "
                    + "The indicated event therefore has probabilities one and zero. No independence is assumed, "
                    + "and these two observations are not claimed to reconstruct every state or law."))),DescribeRole.Theorem),
            Paragraph(Text("For probability measures use TV(mu,nu)=sup_E |mu(E)-nu(E)|=one half of the L1 distance. "
                + "The original laws and their J02 pushforwards each have TV distance one. The unhalved signed variation norm is two.")),
            Paragraph(Text("The finite signed mass space V is additive; its probability simplex M is a subset, not an additive group. "
                + "Each pushforward q_i is directly Mathlib Finsupp.mapDomain.addMonoidHom(delete(i)). "
                + "v=mu-nu is nonzero, for v(X1)=one half, lies in M-M, and satisfies q_i(v)=0 for all four labels. "
                + "Apply ModelRelativeCompletenessDifferenceCriterion.model_relative_completeness_difference_criterion directly to V,q,M; "
                + "M is nonempty because it contains mu. This is the nonzero intersection of the joint additive residual with the model difference set. "
                + "The concrete laws are defined on Cycle(Nat). Identifying them with laws on the fixed-support subtype SupportedCircle({0,1,2,3}) "
                + "is a hand correspondence: the generic criterion application was compiled, but the concrete subtype reindexing "
                + "and its model-difference witness were not compiled as a concrete theorem. "
                + "For three preselected distinct labels on a support of at least four, ThreeSpecifiedDeletions.reconstruct_three instead gives "
                + "injectivity of the same-sample triple map. Apply Finsupp.mapDomain_injective directly to identify all finite signed laws, "
                + "and hence probability laws, from that joint pushforward. Equality of a marginal family is a different condition.")))));
    private static Formula Statement()
    {
        Formula m=F.Id("mu"),n=F.Id("nu"),c=F.Id("C"),i=F.Id("i"),t=Call("Cycle",Call("Nat"));
        Formula supports=All("C",t,Imp(In(c,Call("union",Call("support",m),Call("support",n))),And(Call("Nodup",c),Eq(Call("toFinset",c),Call("set",D(0),D(1),D(2),D(3))))));
        Formula positive=All("C",t,And(Le(D(0),Call("mu",c)),Le(D(0),Call("nu",c))));
        Formula marginals=All("i",Call("Nat"),Imp(In(i,Call("set",D(0),D(1),D(2),D(3))),Eq(Call("push",Call("delete",i),m),Call("push",Call("delete",i),n))));
        return Disp(And(supports,And(positive,And(Eq(Call("mass",m),D(1)),And(Eq(Call("mass",n),D(1)),And(Call("Disjoint",Call("support",m),Call("support",n)),And(marginals,And(Eq(Call("eventProbability",Call("J02"),m),D(1)),Eq(Call("eventProbability",Call("J02"),n),D(0))))))))));
    }
    private static Formula Call(string name,params Formula[] args)=>args.Length==0?new Formula.NamedConstant(FormulaIdentifier.Create(name)):new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)),[..args]);
    private static Formula All(string n,Formula d,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula In(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(Seq(Open,a,Close),FormulaLogicOperator.And,Seq(Open,b,Close));
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(Seq(Open,a,Close),FormulaLogicOperator.Implies,Seq(Open,b,Close));
}
