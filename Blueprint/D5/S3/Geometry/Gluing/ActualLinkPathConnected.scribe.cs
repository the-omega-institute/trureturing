using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class ActualLinkPathConnectedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/ActualLinkPathConnected.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original actual-link vertex-class quotient is path connected in its canonical quotient topology.",
        H("Path connectedness of the full original actual-link quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-link-path-connected"),
                DeclarationHandle.Create(Prefix + "actual_link_path_connected"),
                H("Every original vertex-class link is path connected"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("actual_link_path_connected"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G be arbitrary, let Omega be finite with its arbitrary right G-op action and discrete topology, and choose arbitrary u, v and any original vertex class nu. Point is the unchanged Carrier subtype from ActualLinkCornerChains, and L is exactly Quotient(EqvGen.setoid(Step u v)); L carries the inherited canonical quotient topology.")),
                    Paragraph(Text("For points with one corner tag, the full closed triangle beta(j)=0, beta>=0, sum(beta)=1 is convex. A continuous subtype inclusion followed by the canonical quotient map gives a Joined path in L. For an actual slot ((omega,f),r), choose a unit coordinate k different from the omitted corner j=faceVertex(f,r) and from the crossed face f. The resulting point lies in the original guard, and frozen_face_data together with the unchanged pairedPoint and Step identifies its quotient image with the corresponding point on the actual paired triangle. This is the live common-point bridge for every face and slot, including repeated and self identifications.")),
                    Paragraph(Text("For arbitrary representatives, actual_corner_transport is consumed directly with Unit index, the original endpoint tags, zero real weights and B=0. Its actual Follows list is joined by induction using the same-tag paths and the across-face common point; no reachability or relation correspondence is reproved. Quotient induction then supplies paths between arbitrary quotient points, while Quotient.exists_rep and a coordinate unit vector provide nonemptiness without assuming Omega is nonempty. No transitivity, generation, freeness, regularity, faithfulness or no-self-gluing assumption is introduced."))),
                DescribeRole.Theorem))));

    private static Formula FormulaFor(string name)
    {
        return name switch
        {
            "actual_link_path_connected" => Scope(Implies(
                And(Call("Finite", Id("omega")), Call("DiscreteTopology", Id("omega"))),
                Call("PathConnectedSpace", Call("QuotientTopology",
                    Call("Quotient", Call("EqvGenSetoid", Call("Step", Id("u"), Id("v"), Id("nu")))),
                    Call("SubtypeTopology", Call("Carrier", Id("u"), Id("v"), Id("nu")),
                        Call("ProductTopology", Call("DiscreteCornerTopology", Id("omega")), Call("RealPiTopology", Call("Fin", F.D(4))))))))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }

    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var k = xs.Length - 2; k >= 0; k--)
            r = F.Seq(F.Open, xs[k], F.Close, F.Sp, F.Land, F.Sp, F.Open, r, F.Close);
        return r;
    }
    private static Formula Implies(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Implies, F.Sp, F.Open, b, F.Close);
    private static Formula Scope(Formula body) => All("G", Id("Group"),
        All("omega", Call("RightAction", Id("G")),
            All("u", Id("G"),
                All("v", Id("G"),
                    All("nu", Call("Vertex", Call("pairing", Id("u"), Id("v"))), body)))));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
