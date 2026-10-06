using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class GraphCycleModuleCatDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/GraphCycleModuleCat.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary one-dimensional ModuleCat homology of a finite simple graph is canonically its concrete simple-cycle space.",
        H("ModuleCat Homology of a Binary Graph Cycle Space"),
        Blocks(Describe.Lean(
            DescribeId.Create("graph-cycle-module-cat-homology"),
            DeclarationHandle.Create(Prefix + "graphCycleHomologyIso"),
            H("Graph homology is the binary cycle space"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite vertex type V and a finite simple graph G, the chain object in degree one is "
                        + "the module of binary edge labels. Its differential is the finite linear combination of "
                        + "the two endpoint characters, and the degree-two object is zero. The resulting ShortComplex "
                        + "therefore has a genuine ModuleCat homology object.")),
                Paragraph(Text(
                    "The proof uses Mathlib's explicit ModuleCat homology quotient. The image of the zero degree-two "
                        + "map is bottom, so the quotient is linearly equivalent to the differential kernel. The existing "
                        + "finite-graph cycle-space theorem identifies that kernel with the span of indicators of simple "
                        + "closed cycles, yielding the displayed categorical isomorphism.")),
                Paragraph(Text(
                    "This is the finite binary specialization of the ordinary finite-graph homology/cycle-space "
                        + "correspondence discussed by Diestel and Sprüssel (arXiv:0910.5634, Theorem 21). It does not "
                        + "assert the path-homology quotient used for characteristic different from two, and it does not "
                        + "cover infinite Freudenthal compactifications."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula v = F.Id("V"), g = F.Id("G");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula graph = Call("simpleGraph", v);
        Formula homology = Call("homology", Call("graphCycleComplex", g));
        Formula cycle = Call("ModuleCatOf", Call("ZMod", D(2)), Call("simpleCycleSpace", g));
        return Disp(F.Seq(
            Forall, Sp, v, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("Fintype", v), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Comma, Sp,
            Forall, Sp, g, Colon, Sp, graph, Comma, Sp,
            OpenBracket, Call("Fintype", Call("edgeSet", g)), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", Call("connectedComponent", g)), CloseBracket, Sp,
            homology, Sp, Equiv, Sp, cycle, Dot));
    }
}
