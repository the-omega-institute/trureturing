using System;
using System.Collections.Generic;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CriticalTransitionStarDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/CriticalTransitionStar.critical_transition_star";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A six-occurrence critical edge has strict angle-sum margins on both continuous faces, allowing two transition occurrences.",
        H("Critical opposite floors and a mixed six-valent star"),
        Blocks(
            Paragraph(Text("I is an arbitrary finite type with decidable equality and cardinality six. "
                + "The five functions y,z,o,v,w:I -> Real retain every local occurrence. The target "
                + "coordinate is shared. At each occurrence the order is (12,13,14,34,24,23); "
                + "o is opposite the target and y,z,v,w are its four neighbours. All five "
                + "coordinates lie in [1,2]. ThreeSmall means at least three of the four "
                + "neighbours are at most 5/4, expressed as the four possible conjunctions.")),
            Paragraph(Text("good is a finite subset of I with at least four members. At every good "
                + "occurrence all four neighbours are at most 5/4 and o is at least 4/3. "
                + "No equality of the target and opposite, no prescribed angle and no angle-sum "
                + "inequality is a hypothesis. AngleSum(a,y,z,o,v,w) below abbreviates the sum "
                + "over i:I of arccos(cosine(a,y(i),z(i),o(i),v(i),w(i))). cosine is the "
                + "original six-variable expression from FourCycleEnvelopes, not a free function.")),
            Paragraph(Text("Define beta=arccos(49/sqrt(6534)), gamma=arccos(43/99), and "
                + "margin=min(2pi-6arccos(4/7),4gamma+2beta-2pi). These are exactly the "
                + "three definitions in the paired Lean source.")),
            Describe.Lean(
                DescribeId.Create("critical-transition-continuous-star"),
                DeclarationHandle.Create(Declaration),
                H("Both boundary sums have the same positive margin"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Reuse the derivative-based mixed comparison from the single "
                        + "analytic owner. The lower target 4/3 gives cosine at least 4/7. "
                        + "At target 2 the four possible three-small-neighbour endpoints each "
                        + "give squared cosine 2401/6534. Four small neighbours and opposite "
                        + "floor 4/3 give exactly 43/99. Denominator positivity and square-root "
                        + "comparison are proved within the source.")),
                    Paragraph(Text("For gamma in [0,pi/2], cos(2gamma)=-6103/9801. The positive "
                        + "square comparison (6103/9801)^2-2401/6534=3896615/192119202 proves "
                        + "2gamma>pi-beta. This gives 4gamma+2beta>2pi. The lower gap follows "
                        + "from 4/7>cos(pi/3). Summing beta plus the good-occurrence increment "
                        + "gamma-beta, and using card(good)>=4, gives the actual six-occurrence "
                        + "upper-face bound. It is not a theorem with the desired budget assumed.")),
                    Paragraph(Text("The quantified functions vary over continuous faces. Pullbacks "
                        + "of one shared global length vector are included among these functions; "
                        + "the source does not construct the global incidence carrier or prove "
                        + "manifold links, co-volume existence or the full CFMP conjecture. "
                        + "The ordinary application uses favourable opposites of the same degree "
                        + "class, so it is preserved by unbranched covers even when global "
                        + "edge identities split. This candidate and its existing dependency "
                        + "have no Lean compilation receipt here; this authored Scribe is also uncompiled."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var i=F.Id("i"); var I=F.Id("I"); var g=F.Id("good");
        string[] names=["y","z","o","v","w"];
        var fs=names.Select(name=>F.Id(name)).ToArray();
        var values=fs.Select(f=>Call("apply",f,i)).ToArray();
        var box=All([("i",I)],And([..values.Select(x=>In(x,F.D(1),F.D(2)))]));
        var small=All([("i",I)],Call("ThreeSmall",values[0],values[1],values[3],values[4]));
        var paired=All([("i",I)],Imp(Member(i,g),And(
            Le(values[0],Rat(5,4)),Le(values[1],Rat(5,4)),
            Le(values[3],Rat(5,4)),Le(values[4],Rat(5,4)),Le(Rat(4,3),values[2]))));
        var premises=And(Eq(Call("card",I),F.D(6)),Le(F.D(4),Call("card",g)),box,small,paired);
        var m=F.Id("margin"); var twoPi=Call("mul",F.D(2),F.Id("pi"));
        var lower=Call("AngleSum",[Rat(4,3),..fs]);
        var upper=Call("AngleSum",[F.D(2),..fs]);
        var result=And(Lt(F.D(0),m),Le(lower,Call("sub",twoPi,m)),Le(Call("add",twoPi,m),upper));
        var variables=new List<(string Name,Formula Type)>{("I",F.Id("FiniteType"))};
        variables.AddRange(names.Select(name=>(name,Call("Functions",I,F.Id("Real")))));
        variables.Add(("good",Call("Finset",I)));
        return All([..variables],Imp(premises,result));
    }

    private static Formula All((string Name,Formula Type)[] vs,Formula body)=>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..vs.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(params Formula[] p)
    {
        if(p.Length==0) throw new ArgumentException("Empty conjunction");
        var r=p[^1]; for(var j=p.Length-2;j>=0;j--) r=new Formula.Logic(p[j],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Member(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula In(Formula x,Formula a,Formula b)=>Member(x,Call("Icc",a,b));
    private static Formula Rat(int n,int d)=>F.Seq(F.Frac,F.Grp(F.D(n)),F.Grp(F.D(d)));
    private static Formula Call(string name,params Formula[] args)
    {
        var p=new List<Formula>{F.Operatorname,F.Grp(F.Id(name)),F.Open};
        for(var j=0;j<args.Length;j++){if(j>0)p.AddRange([F.Comma,F.Sp]);p.Add(args[j]);}
        p.Add(F.Close);return F.Seq([..p]);
    }
}
