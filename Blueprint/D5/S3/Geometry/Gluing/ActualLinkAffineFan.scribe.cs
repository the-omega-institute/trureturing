using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class ActualLinkAffineFanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/ActualLinkAffineFan.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordered-corner occurrences carry strict affine sector coordinates.",
        H("Actual strict-sector affine coordinates"),
        Blocks(
            Def("Sector", "The strict triangle sector",
                "The two real coordinates are nonnegative and their sum is strictly less than one. This is the open radial part of the closed triangle, with both seam edges and the origin retained."),
            Def("beta", "Source barycentric coordinates",
                "For row c and phase s, the omitted corner has coordinate zero, the ordered tip has coordinate 1-(a+b)/2, the incoming face has a/2, and the outgoing face has b/2. The four labels are distinct in each of the twelve actual ordered endpoint positions."),
            Def("vertex", "The actual seed corner class",
                "The vertex is the original pairing label of the corner of encode(u,v,c,(x,0)). All four rows retain the source order L0, L1, H2, H0, and ordered pairs such as (3,0) are not sorted."),
            Def("rawPhi", "Finite occurrence coordinates",
                "The index lies in Fin(3r), where r is the minimal point period of the original row return word at x. Its actual dart is occurrence(u,v,c,x,i). The phase of the corresponding iterate of tour determines the incoming and outgoing face coordinates. No return of the full transported frame is required."),
            Def("Phi", "The strict original neighborhood",
                "Restrict a and b to nonnegative reals with a+b<1. The constructed raw point lies in the original Carrier at the actual seed vertex and in Neighborhood of the actual seed dart. Its ordered tip has barycentric coordinate strictly greater than one half. The cutoff a+b=1 is outside this chart; it is not removed from the ambient carrier."),
            Describe.Lean(DescribeId.Create("actual-strict-coordinate-bijection"),
                DeclarationHandle.Create(Prefix + "actual_strict_coordinates"),
                H("Unique actual occurrence and affine coordinates"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("actual_strict_coordinates"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any group G, any finite set Omega with a right G action, any u and v, any one of the four rows, and any root x, Phi bijectively parametrizes the genuine strict original neighborhood. There is no assumption that G is finite, that the action is faithful, free, transitive or regular, or that the return word has finite group order.")),
                    Paragraph(Text("The inverse first finds the unique barycentric coordinate greater than one half. The original ordered-dart component enumeration then determines the unique occurrence index. The two real coordinates are twice the original incoming and outgoing barycentric coordinates. The simplex equation and zero omitted-corner coordinate prove that their sum is strictly less than one and reconstruct every original barycentric entry.")),
                    Paragraph(Text("The original pairedPoint construction transports the corner label along each guarded dart step; EqvGen induction transports it along the complete dart component. This puts Phi at the same actual link vertex, not at an independently chosen label. The finite-period supplier covers singleton period one, giving three occurrences, as well as nonfaithful and nonregular actions.")),
                    Paragraph(Text("This result constructs coordinates before quotienting. It does not prove that original affine Step is a cyclic seam or its reverse, identify full affine EqvGen with the cyclic fan relation, prove continuity of these coordinates, or give the saturated quotient open disk chart. The original truncation-slice comparison and the global orientability, closedness, genus and geometric conclusions remain separate.")),
                    Paragraph(Text("The source is the actual link application accompanying supplement 122.3 of the group-transport construction. ActualCornerPointPeriods supplies the entire original dart component, and ActualLinkCornerChains supplies the original guarded affine carrier. The cyclic fan disk theorem is an existing further supplier; no generic circle or disk theorem is proved here. No literature-priority claim is made."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Def(string name, string heading, string text) =>
        Describe.Lean(DescribeId.Create("actual-link-affine-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(F.Disp(FormulaFor(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula FormulaFor(string name)
    {
        var g=F.Id("G"); var o=F.Id("Omega"); var u=F.Id("u"); var v=F.Id("v");
        var c=F.Id("c"); var x=F.Id("x"); var s=F.Id("s"); var p=F.Id("p");
        var l=F.Id("l"); var z=F.Id("z");
        var f4=Call("Fin",F.D(4)); var f3=Call("Fin",F.D(3));
        var index=Call("Fin",Product(F.D(3),Call("pointPeriod",u,v,c,x)));
        var source=Product(index,F.Id("Sector"));
        var seed=Call("encode",u,v,c,Tuple(x,F.D(0)));
        var phase=Call("second",Call("iterate",Call("tour",u,v,c),Call("value",Call("first",z)),Tuple(x,F.D(0))));
        var raw=Tuple(Call("first",Call("occurrence",u,v,c,x,Call("first",z))),
            Call("beta",c,phase,Call("value",Call("second",z))));
        var target=Call("Neighborhood",u,v,Call("vertex",u,v,c,x),seed);
        Formula Scope(Formula body) => All("G",F.Id("Group"),All("Omega",Call("RightAction",g),
            All("u",g,All("v",g,All("c",f4,All("x",o,body))))));
        var a=Call("first",p); var b=Call("second",p);
        var betaValue=Call("if",Eq(l,Call("tip",c,s)),
            Call("subtract",F.D(1),Call("divide",Call("add",a,b),F.D(2))),
            Call("if",Eq(l,Call("incoming",c,s)),Call("divide",a,F.D(2)),
                Call("if",Eq(l,Call("outgoing",c,s)),Call("divide",b,F.D(2)),F.D(0))));
        return name switch
        {
            "Sector" => All("p",Product(F.Id("Real"),F.Id("Real")),
                Iff(Call("member",p,F.Id("Sector")),And(
                    F.Seq(F.D(0),F.Sp,F.Le,F.Sp,a),F.Seq(F.D(0),F.Sp,F.Le,F.Sp,b),
                    Lt(Call("add",a,b),F.D(1))))),
            "beta" => All("c",f4,All("s",f3,All("p",Product(F.Id("Real"),F.Id("Real")),
                All("l",f4,Eq(Call("beta",c,s,p,l),betaValue))))),
            "vertex" => Scope(Eq(Call("vertex",u,v,c,x),Call("label",Call("pairing",u,v),Call("first",seed)))),
            "rawPhi" => Scope(All("z",source,Eq(Call("rawPhi",u,v,c,x,z),raw))),
            "Phi" => Scope(Implies(Call("Finite",o),All("z",source,And(
                Call("member",Call("Phi",u,v,c,x,z),target),
                Eq(Call("underlyingRaw",Call("Phi",u,v,c,x,z)),raw))))),
            "actual_strict_coordinates" => Scope(Implies(Call("Finite",o),
                Call("Bijective",Call("Phi",u,v,c,x)))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[.. args]);
    private static Formula Tuple(params Formula[] xs)
    {
        var parts = new System.Collections.Generic.List<Formula> { F.Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { parts.Add(F.Comma); parts.Add(F.Sp); }
            parts.Add(xs[i]);
        }
        parts.Add(F.Close);
        return F.Seq([.. parts]);
    }
    private static Formula Product(Formula a, Formula b) => F.Seq(a,F.Sp,F.Times,F.Sp,b);
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length-2; i >= 0; i--) r = new Formula.Logic(xs[i],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
}
