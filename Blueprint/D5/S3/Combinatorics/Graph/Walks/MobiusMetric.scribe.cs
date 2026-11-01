using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class MobiusMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Antipodal translation reduces native shortest paths to two cyclic alternatives.", H("All-size native Mobius metrics and diameters"), Blocks(
            Paragraph(Text("Put r=m+2 and z=(v-u).val in ZMod(2r). The native distance is min(min(z,2r-z), 1+min(Nat.dist(r,z),2r-Nat.dist(r,z))). The spanning unit-jump cycle is connected. Antipodal translation is an involutive automorphism of that cycle, and its matching extension equals the native Mobius graph.")),
            Node("mobius_distance", "Exact cyclic-difference metric",
                All("m",C("Nat"),All("u",C("ZMod",C("mul",D(2),C("add",I("m"),D(2)))),All("v",C("ZMod",C("mul",D(2),C("add",I("m"),D(2)))),Eq(C("dist",C("mobius",I("m")),I("u"),I("v")),C("MobiusMetricFormula",I("m"),I("u"),I("v")))))),
                "The notation MobiusMetricFormula denotes precisely the minimum displayed in the preceding paragraph, with r=m+2 and z=(v-u).val. The proof reuses the public cycle-distance theorem and length-preserving graph-isomorphism distance transport, then applies the involutive matching normal form."),
            Node("mobius_diameter", "The sharp diameter at every size",
                All("m",C("Nat"),Eq(C("diam",C("mobius",I("m"))),C("NatDiv",C("add",I("m"),D(3)),D(2)))),
                "The metric formula bounds every distance by floor((m+3)/2). The actual cyclic vertex with value floor((m+3)/2), paired with zero, attains that bound. This proves all sizes at once, including diameters one, two and two for the first three Mobius ladders.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/MobiusMetric." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
