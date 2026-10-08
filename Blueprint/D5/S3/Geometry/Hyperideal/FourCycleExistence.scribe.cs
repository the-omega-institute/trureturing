using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every four-cycle incidence system has one shared interior zero-curvature vector.",
        H("A simultaneous solution for all global edge equations"),
        Blocks(
            Paragraph(Text("Let T be a finite type of tetrahedra and E a type of global edge labels "
                + "with decidable equality. The incidence s assigns a label to each of the six local "
                + "edges of every tetrahedron and a low/high colour to each global label. "
                + "FourCycle(s) requires the four low slots to form the prescribed local cycle, "
                + "degree eight at each low label, and degree at least twelve at each high label. "
                + "Degrees are actual fibre cardinalities, including repeated occurrences.")),
            Paragraph(Text("The lower and upper endpoints L(s) and U(s), local cosine C(s,x,o), "
                + "and curvature K(s,x,e) are exactly those of FourCycleCurvature. "
                + "In particular, each local coordinate reads the same global vector x:E -> Real. "
                + "K is 2pi minus the sum of arccos(C) over the actual occurrence fibre.")),
            Describe.Lean(
                DescribeId.Create("fourcycle-shared-zero-curvature"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/FourCycleExistence.fourcycle_zero_curvature"),
                H("An interior vector with all angle sums equal to 2pi"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every global label has a nonempty finite occurrence fibre, "
                        + "so the incidence map is surjective and the edge-label type is finite. "
                        + "This finiteness is derived from FourCycle(s); it is not an additional hypothesis.")),
                    Paragraph(Text("The established box has strictly positive radicands, "
                        + "strictly admissible cosines, and inward curvature margins on all faces. "
                        + "Polynomial operations, square roots away from zero, division and arccos "
                        + "make the actual shared curvature map continuous on this box.")),
                    Paragraph(Text("Normalize the box to a unit cube. The cube is a retract of "
                        + "a simplex: divide its n coordinates by n+1, append the slack coordinate "
                        + "one minus their sum, and project back by multiplying the n non-slack weights "
                        + "by n+1 and clamping to [0,1]. The classical simplex fixed-point theorem "
                        + "therefore applies to the clamped curvature self-map. Strict face signs "
                        + "exclude every boundary coordinate of its fixed point; interior clamp "
                        + "cancellation then forces every curvature to vanish.")),
                    Paragraph(Text("The conclusion concerns the real incidence system. "
                        + "It does not assert that arbitrary incidence data form a manifold, "
                        + "supply face pairings or vertex-link conditions, or prove unrestricted CFMP. "
                        + "The geometric interpretation of the cosine formula and the passage to "
                        + "a complete hyperbolic realization retain their separate hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t=F.Id("T"); var eType=F.Id("E"); var s=F.Id("s");
        var x=F.Id("x"); var e=F.Id("e"); var o=F.Id("o");
        var interior=All([("e",eType)],And(
            Lt(Apply(Call("L",s),e),Apply(x,e)),
            Lt(Apply(x,e),Apply(Call("U",s),e))));
        var cosine=Call("C",s,x,o);
        var strict=All([("o",Call("Product",t,Call("Fin",F.D(6))))],And(
            Lt(F.Seq(F.Minus,F.D(1)),cosine),Lt(cosine,F.D(1))));
        var zero=All([("e",eType)],Eq(Call("K",s,x,e),F.D(0)));
        var exists=new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("x"),
                new Formula.TypeArrow(eType,F.Id("Real")))],And(interior,strict,zero));
        return All([("T",F.Id("Type")),("E",F.Id("Type")),
            ("s",Call("Incidence",t,eType))],
            Imp(And(Call("Fintype",t),Call("DecidableEq",eType),Call("FourCycle",s)),exists));
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
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Apply(Formula function,params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula Call(string name,params Formula[] args)=>Apply(F.Id(name),args);
}
