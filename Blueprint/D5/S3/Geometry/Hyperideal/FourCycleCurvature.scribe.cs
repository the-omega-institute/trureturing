using System;
using System.Collections.Generic;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleCurvatureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleCurvature.fourcycle_curvature_box";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual occurrence-counted curvature has a uniform inward margin on an explicit global four-cycle box.",
        H("From local angle envelopes to all global curvature faces"),
        Blocks(
            Paragraph(Text("T and E are arbitrary finite types of tetrahedra and global edges. "
                + "An incidence s has edge:T -> Fin(6) -> E and low:E -> Bool. In the local "
                + "order (12,13,14,34,24,23), slots 0 and 3 are high and the other four are low. "
                + "FourCycle(s) requires this equality at every local slot, degree eight for "
                + "every low global label, and degree at least twelve for every high label. "
                + "Degree is the actual cardinality of the fibre of edge, including repeated labels.")),
            Paragraph(Text("For each local target, frame is an explicit permutation induced by "
                + "a tetrahedral vertex relabeling. Its zeroth coordinate is the target; for "
                + "a low target its slots 0,1,3,4 are low. All frame coordinates read the SAME "
                + "global vector x:E -> Real. C(s,x,o) is the previous exact six-variable cosine "
                + "after this relabeling. The angle is arccos(C), and K(s,x,e) is 2pi minus "
                + "the sum over all occurrences o with source e.")),
            Paragraph(Text("Set m=card(T x Fin(6)), t=pi/(m+2), c=cos(t), and "
                + "delta(T)=min(1/8,(1-c)/(2+c)). The lower vector L(s) has value 5/4 "
                + "at low labels and 1+delta at high labels. U(s) has value 2 at low labels "
                + "and 8/5 at high labels. Box(s,x) means L(s)(e)<=x(e)<=U(s)(e) for all e. "
                + "The size-independent eta is min(pi, min(2pi-8arccos(293/400), "
                + "min(8arccos(1577/2236)-2pi,12arccos(37/43)-2pi))).")),
            Describe.Lean(
                DescribeId.Create("fourcycle-global-curvature-box"),
                DeclarationHandle.Create(Declaration),
                H("An explicit nonempty box with signed margin on every face"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The derivative-based local theorem is consumed directly. "
                        + "The proof checks the actual finite frame permutations, proves the "
                        + "trigonometric gaps from exact square-root comparisons, and constructs "
                        + "delta rather than assuming an unspecified sufficiently small number. "
                        + "It proves cos(t)<2(1-delta)/(2+delta), so on a high lower face each "
                        + "angle is below t. There are at most m occurrences at any edge; hence "
                        + "the angle sum is below pi and its curvature exceeds pi.")),
                    Paragraph(Text("On low lower and upper faces the exact cardinality is eight. "
                        + "The corresponding arccos bounds are summed over the actual fibre. "
                        + "On a high upper face the cardinality is at least twelve and all "
                        + "arccos values are nonnegative. These give the three fixed gaps in eta. "
                        + "The same proof shows -1<C(s,x,o)<1 throughout the box, and the lower "
                        + "vector itself witnesses nonemptiness. No solution or face sign is assumed.")),
                    Paragraph(Text("This is a real incidence-system theorem. The formal statement "
                        + "does not certify that the incidence system is a manifold, prove the "
                        + "hyperbolic realization of each angle formula, or invoke an unproved "
                        + "Brouwer or co-volume existence axiom. Those geometric identifications "
                        + "and the ordinary variational existence step remain separate."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var s=F.Id("s"); var x=F.Id("x"); var e=F.Id("e"); var o=F.Id("o");
        var delta=Call("delta",F.Id("T")); var eta=F.Id("eta");
        var lower=Call("L",s); var upper=Call("U",s);
        var c=Call("C",s,x,o); var k=Call("K",s,x,e);
        var nondeg=All([("o",Call("Product",F.Id("T"),Call("Fin",F.D(6))))],
            And(Lt(F.Seq(F.Minus,F.D(1)),c),Lt(c,F.D(1))));
        var faces=All([("e",F.Id("E"))],And(
            Imp(Eq(Call("apply",x,e),Call("apply",lower,e)),Le(eta,k)),
            Imp(Eq(Call("apply",x,e),Call("apply",upper,e)),Le(k,F.Seq(F.Minus,eta)))));
        var conclusion=And(Lt(F.D(0),delta),Le(delta,Rat(1,8)),Lt(F.D(0),eta),
            Call("Box",s,lower),All([("x",Call("Functions",F.Id("E"),F.Id("Real")))],
                Imp(Call("Box",s,x),And(nondeg,faces))));
        return All([("T",F.Id("FiniteType")),("E",F.Id("FiniteType")),
            ("s",Call("Incidence",F.Id("T"),F.Id("E")))],
            Imp(Call("FourCycle",s),conclusion));
    }

    private static Formula All((string Name,Formula Type)[] variables,Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(params Formula[] p)
    {
        if(p.Length==0) throw new ArgumentException("Empty conjunction");
        var q=p[^1]; for(var i=p.Length-2;i>=0;i--) q=new Formula.Logic(p[i],FormulaLogicOperator.And,q);
        return q;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Rat(int n,int d)=>F.Seq(F.Frac,F.Grp(F.D(n)),F.Grp(F.D(d)));
    private static Formula Call(string name,params Formula[] args)
    {
        var p=new List<Formula>{F.Operatorname,F.Grp(F.Id(name)),F.Open};
        for(var i=0;i<args.Length;i++){if(i>0)p.AddRange([F.Comma,F.Sp]);p.Add(args[i]);}
        p.Add(F.Close);return F.Seq([..p]);
    }
}
