using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class PolygonMarkedEndpointChainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/PolygonMarkedEndpointChains.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked endpoints in the actual circular polygon quotient: saturation and complete chain reflection.",
        H("Circular polygon endpoint chains"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygon-endpoint-step"),
                DeclarationHandle.Create(Prefix + "EndpointStep"), H("Occurrence-sensitive endpoint instructions"),
                StatementSource.FromAuthor(F.Disp(EndpointStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An endpoint occurrence is the initial endpoint of one labelled side. The terminal endpoint is the initial endpoint of its cyclic successor. Each supplied gluing instruction contributes its two endpoint identifications: the same parameter direction preserves the endpoint bit, and the opposite direction complements it. No quotient-vertex labels, distinct geometric vertices, regular action or manifold assumptions enter this definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-marked-endpoint-chains"),
                DeclarationHandle.Create(Prefix + "polygon_marked_endpoint_chains"),
                H("All intermediate point representatives remain marked endpoints"),
                StatementSource.FromAuthor(F.Disp(MainStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every type of faces, every natural side-count function and every set of the actual PolygonGluing.Identification instructions, the marked locus is saturated under the full generated point relation. For every two marked vertices, the full polygon point relation holds exactly when the explicit EndpointStep instructions generate a chain between their side occurrences. Face types and instruction sets may be infinite. A face with zero sides contributes no marked endpoint; monogons, digons, loops, repeated incidences, unpaired sides and multiple instructions remain in scope.")),
                    Paragraph(Text("The geometric input uses the original PolygonCell closed complex disk and its circular side parametrization. Circle.exp_eq_exp forces a side point equal to a marked vertex to have endpoint parameter zero or one. Circle.exp_injOn_Ico supplies uniqueness of the initial marked endpoint index. These facts lift each generator, and saturation supplies the intermediate marked representative at every transitive step. The reverse chain direction uses the actual two endpoint instances of each polygon generator.")),
                    Paragraph(Text("The cell, side, instruction and generated-relation definitions are a minimal source selection from mccorvie/classification-of-surfaces at e3c7230fe78d7b056a415d9ecae6f77887046b32, PolygonalQuotient.lean, under Apache-2.0. Their original namespaces and definitions are preserved. Copied convenience theorems are omitted, and the consumed boundary calibration proof is reused at its source. This adaptation does not install or upgrade the donor project.")),
                    Paragraph(Text("This is an independent endpoint core. It does not construct the original nu-restricted finite cyclic presentation, its list-word validity or connectivity certificate, the calibrated original Point pre-space homeomorphism, or either full-point generator correspondence. Those remain the required full-point and presentation interfaces for the chosen normalization result; the marked endpoint relation can be compared separately to the original return-cycle quotient. No Euler characteristic, genus, closed-manifold, orientation or full CFMP completion follows from this theorem alone."))),
                DescribeRole.Theorem))));

    private static Formula Face => Id("Face");
    private static Formula Count => Id("count");
    private static Formula I => Id("I");
    private static Formula Side => Call("Side", Face, Count);
    private static Formula Pre => Call("PreRealization", Face, Count);
    private static Formula Instructions => Call("Identification", Face, Count);
    private static Formula Marked(Formula x) => Exists("s", Side,
        Eq(x, Call("point", Id("s"), F.D(0))));
    private static Formula Rel(Formula x, Formula y) => Call("PolygonRelation", I, x, y);
    private static Formula EndpointStatement()
    {
        var a = Id("a");
        var b = Id("b");
        var instructions = And(Call("Member", a, I),
            Eq(Id("s"), Call("endSide", Call("source", a), b)),
            Eq(Id("t"), Call("endSide", Call("target", a),
                Call("endDirection", Call("direction", a), b))));
        return Scope(All("s", Side, All("t", Side,
            Iff(Call("EndpointStep", I, Id("s"), Id("t")),
                Exists("a", Instructions, Exists("b", Id("Bool"), instructions))))));
    }
    private static Formula MainStatement()
    {
        var saturation = All("x", Pre, All("y", Pre,
            Implies(Rel(Id("x"), Id("y")), Iff(Marked(Id("x")), Marked(Id("y"))))));
        var reflection = All("s", Side, All("t", Side, Iff(
            Rel(Call("point", Id("s"), F.D(0)), Call("point", Id("t"), F.D(0))),
            Call("EqvGen", Call("EndpointStep", I), Id("s"), Id("t")))));
        return Scope(And(saturation, reflection));
    }
    private static Formula Scope(Formula body) => All("Face", Id("Type"),
        All("count", Call("Functions", Face, Id("Nat")),
            All("I", Call("Set", Instructions), body)));
    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula Eq(Formula a, Formula b) => F.Seq(a, F.Sp, F.Eq, F.Sp, b);
    private static Formula Iff(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Iff, F.Sp, F.Open, b, F.Close);
    private static Formula Implies(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Implies, F.Sp, F.Open, b, F.Close);
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var k = xs.Length - 2; k >= 0; k--)
            r = F.Seq(F.Open, xs[k], F.Close, F.Sp, F.Land, F.Sp, F.Open, r, F.Close);
        return r;
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
