using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class PairedTriangleCornerCyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local corner occurrences over each quotient vertex have a positive cyclic coordinate with an explicit permutation-power formula.",
        H("Corner cycles of finitely paired triangles"),
        Blocks(
            Paragraph(Text("F is any finite type of triangle occurrences. A side is a pair (face,s), "
                + "with s in Fin(3), opposite corner s. Its two endpoint occurrences are listed by "
                + "sideCorner(0)=(1,2), sideCorner(1)=(2,0), sideCorner(2)=(0,1). Pairing gives a "
                + "fixed-point-free involution on side occurrences and an endpoint permutation on "
                + "each side. The endpoint permutations on paired sides are inverses. No "
                + "injectivity of quotient corner labels or distinctness of face labels is assumed.")),
            Paragraph(Text("A flag is a side occurrence with one of its two endpoints. Cross applies "
                + "the side pairing and its endpoint permutation. Turn exchanges the two flags "
                + "meeting at the same corner of the same triangle. Write a=Cross, b=Turn, "
                + "p=b*a, with the right factor applied first, and c=cornerProjection. The vertex "
                + "relation is exactly the equivalence closure of c(f)~c(a(f)). CornerFiber(q,f) "
                + "is the subtype of local corner occurrences d whose vertexClass equals that "
                + "of c(f). It retains separate local corner occurrences even if their vertex "
                + "images coincide.")),
            Describe.Lean(
                DescribeId.Create("paired-triangle-corner-cycle"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Gluing/PairedTriangleCornerCycles.actual_corner_cycle"),
                H("Positive corner-cycle coordinates"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The construction takes n to be the least positive period of p at "
                        + "that flag. The forward coordinate is c(p^i(f)). Every actual local "
                        + "corner occurrence in the fiber occurs at exactly one index. The "
                        + "two flags of one local corner form a turn pair. The proof first "
                        + "shows that every matching-connected flag lies either in the p-orbit "
                        + "of f or in its turn row; this coverage follows by transporting a "
                        + "two-orbit invariant along arbitrary generated paths. Orbit separation "
                        + "and minimal-period injectivity then give unique coordinates.")),
                    Paragraph(Text("The orbit-separation proof is adapted from William Whistler's "
                        + "RS.relPairing_not_sameCycle in LeanPool/lean-pool, revision "
                        + "766a994003f161b1013109977cd615b06d0dd5a9, under Apache 2.0. "
                        + "It supplies separation for two fixed-point-free involutions. "
                        + "Mathlib supplies individual orbit laws, periodicity and minimal-period "
                        + "coordinates. The two-orbit coverage and the connection to the "
                        + "displayed triangle corner quotient are the additional deductions.")),
                    Paragraph(Text("The construction includes n=1 and n=2. Parallel side pairings, "
                        + "self-pairings between distinct sides of one triangle, repeated face "
                        + "labels in a component, and equal images of different local corners "
                        + "are allowed. Empty F contributes no input flags. This is a finite "
                        + "incidence result for the stated Pairing interface. It proves no "
                        + "geometric collars, restricted geometric relation saturation, "
                        + "quotient homeomorphism, open surface charts, global orientability, "
                        + "surface classification or Euler/genus formula."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var type=F.Id("Type"); var faces=F.Id("F"); var q=F.Id("q"); var flag=F.Id("f");
        var n=F.Id("n"); var e=F.Id("e"); var i=F.Id("i");
        var fin=Call("Fin",n);
        var fiber=Call("CornerFiber",q,flag);
        var cross=Call("Cross",q);
        var turn=F.Id("Turn");
        var walk=new Formula.Binary(turn,FormulaBinaryOperator.Multiply,cross);
        var point=Apply(new Formula.Power(walk,i),flag);
        var coordinates=All([("i",fin)],Eq(Apply(e,i),Call("cornerProjection",point)));
        var result=Exists([("n",F.Id("Nat"))],And(
            new Formula.Relation(F.D(0),FormulaRelationOperator.LessThan,n),
            Exists([("e",Call("Equiv",fin,fiber))],coordinates)));
        return All([("F",type)],new Formula.Logic(Call("Finite",faces),FormulaLogicOperator.Implies,
            All([("q",Call("Pairing",faces)),("f",Call("Flag",faces))],result)));
    }
    private static Formula All((string Name,Formula Type)[] vs,Formula body)=>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..vs.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula Exists((string Name,Formula Type)[] vs,Formula body)=>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [..vs.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Apply(Formula f,params Formula[] args)=>new Formula.Apply(f,[..args]);
    private static Formula Call(string name,params Formula[] args)=>Apply(F.Id(name),args);
}
