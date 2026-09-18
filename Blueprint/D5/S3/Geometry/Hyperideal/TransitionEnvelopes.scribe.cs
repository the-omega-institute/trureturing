using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class TransitionEnvelopesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/TransitionEnvelopes.transition_envelopes";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous upper-face bounds for unbalanced tetrahedral transitions and a high-edge occurrence budget.",
        H("Mixed transition angle envelopes"),
        Blocks(
            Paragraph(Text("All variables are real. The exact function cosine is imported from "
                + "FourCycleEnvelopes in local order (12,13,14,34,24,23), so x and o are opposite. "
                + "It is P/sqrt(A)/sqrt(B), where P=yz+vw+xyv+xzw-(x^2-1)o, "
                + "A=2xyw+x^2+y^2+w^2-1 and B=2xzv+x^2+z^2+v^2-1.")),
            Paragraph(Text("TwoSmall(y,z,v,w) means at least two of these four independently "
                + "varying neighbours are at most 5/4. OneSmall means at least one is at most "
                + "5/4. Every quantified coordinate, including the opposite coordinate o, also "
                + "lies in the closed interval [1,2]. No endpoint or monotonicity condition is "
                + "added as a hypothesis.")),
            Describe.Lean(
                DescribeId.Create("mixed-transition-whole-face-bounds"),
                DeclarationHandle.Create(Declaration),
                H("Two short neighbours and one short neighbour"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use the shared mixed-coordinate comparison, whose owner "
                        + "derives its derivative sign from the original six-variable expression. "
                        + "For the low upper face x=2, split the six possible choices of two "
                        + "short neighbours. Move just those two upper endpoints to 5/4, the "
                        + "other two to 2, and the opposite lower endpoint to 1. The three "
                        + "arrangement values are 67/99, 70/99 and sqrt(128/297); the proof "
                        + "verifies their common bound using the actual radicands and numerator.")),
                    Paragraph(Text("The high upper face x=5/4 has four possible short-neighbour "
                        + "positions. Each endpoint has positive numerator 225/16 and squared "
                        + "denominator 29403/128, hence squared quotient 625/726. An internal "
                        + "positive-square-root argument justifies comparison of the quotient "
                        + "with 25/sqrt(726), without dropping signs or assuming a division is legal.")),
                    Paragraph(Text("The theorem covers continuous faces and independently "
                        + "varying coordinates. It is used in the ordinary mixed-incidence "
                        + "realization proof in CFMP_GEOMETRIC_REALIZATION.md Section 25. "
                        + "The seventeen-degree angle budget, topological face pairing and "
                        + "global co-volume minimizer are outside this formal declaration. "
                        + "It does not certify those geometric steps."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        string[] names=["y","z","o","v","w"];
        var a=names.Select(name=>F.Id(name)).ToArray();
        var intervals=a.Select(t=>In(t,F.D(1),F.D(2))).ToArray();
        var two=ForAll(names,Imp(And([..intervals,Call("TwoSmall",a[0],a[1],a[3],a[4])]),
            Le(Call("cosine",F.D(2),a[0],a[1],a[2],a[3],a[4]),Rat(70,99))));
        var one=ForAll(names,Imp(And([..intervals,Call("OneSmall",a[0],a[1],a[3],a[4])]),
            Le(Call("cosine",Rat(5,4),a[0],a[1],a[2],a[3],a[4]),
                F.Seq(F.Frac,F.Grp(F.D(2,5)),F.Grp(Call("sqrt",Number(726)))))));
        return And(two,one);
    }

    private static Formula ForAll(string[] names,Formula body)=>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..names.Select(name=>new Formula.BoundVariable(FormulaIdentifier.Create(name),
                new Formula.NamedConstant(FormulaIdentifier.Create("Real"))))],body);
    private static Formula And(params Formula[] clauses)
    {
        if(clauses.Length==0) throw new ArgumentException("Empty conjunction");
        var result=clauses[^1];
        for(var i=clauses.Length-2;i>=0;i--)
            result=new Formula.Logic(clauses[i],FormulaLogicOperator.And,result);
        return result;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula In(Formula x,Formula a,Formula b)=>new Formula.Relation(x,FormulaRelationOperator.MemberOf,Call("Icc",a,b));
    private static Formula Rat(int n,int d)=>F.Seq(F.Frac,F.Grp(Number(n)),F.Grp(Number(d)));
    private static Formula Number(int value) => value switch
    {
        4 => F.D(4), 5 => F.D(5), 70 => F.D(7, 0), 99 => F.D(9, 9),
        726 => F.D(7, 2, 6),
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
    private static Formula Call(string name,params Formula[] args)
        => new Formula.Apply(F.Id(name), [.. args]);
}
