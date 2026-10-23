using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamEndpointRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer endpoint multiplicity from actual numbered refinement.",
        H("Integer endpoint multiplicity from actual numbered refinement"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("numbered-integer-adjacency"),
                DeclarationHandle.Create(Prefix + "adjacency"),
                H("Count outgoing edges with multiplicity"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Apply(Call("adjacency", I("G")), I("u")),
                                Call("outgoingBasisSum", I("G"), I("u"))),
                            B("u", I("V"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("adjacency G is Matrix V V Int. outgoingBasisSum(u) is the sum over e : {e:E // G.source e=u} of Pi.single (G.target e.val) 1. Each parallel numbered edge contributes separately. wordRow sums the endpoint basis vector of every length-r Continuation; wordRow_eq_pow computes it as Pi.single u 1 multiplied on the right by adjacency G raised to r."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("intrinsic-endpoint-multiplicity-row"),
                DeclarationHandle.Create(Prefix + "endpointRow"),
                H("One integer basis contribution per intrinsic ray"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call("endpointRow", I("G"), I("U"), I("n")),
                                Call("intrinsicEndpointSum", I("G"), I("U"), I("n"))),
                            B("U", Call("Set", Call("History", I("G")))),
                            B("n", I("Int")),
                            B("finiteParts", Call("Finite", Call("Parts", I("G"), I("U"), I("n"))))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("intrinsicEndpointSum is the finite sum over P : Parts G U n of Pi.single (RayAt.endpoint G P.val) 1, an element of V -> Int. The finiteParts binder is the local Finite instance required by endpointRow. Multiple distinct pasts ending at the same vertex increase that integer coefficient. An actual finite disjoint union of same-cut rays has exactly one term per union index by endpointRow_disjointUnion; the disjointness premise is essential for that formula."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("unbounded-intrinsic-row-refinement"),
                DeclarationHandle.Create(Prefix + "endpointRow_refine"),
                H("The actual row advances on the right by each nonnegative power"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call("endpointRow", I("G"), I("U"), Call("laterCut", I("n"), I("r"))),
                                Call(
                                    "rightMultiply",
                                    Call("endpointRow", I("G"), I("U"), I("n")),
                                    Call("power", Call("adjacency", I("G")), I("r")))),
                            B("U", Call("Set", Call("History", I("G")))),
                            B("n", I("Int")),
                            B("hU", Call("AtCut", I("G"), I("U"), I("n"))),
                            B("r", I("Nat"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("laterCut(n,r) is n+(r:Int); rightMultiply is Matrix.vecMul, so c_(n+r)=c_n B^r. The endpointRow calls install the Finite instances from hU and atCut_mono hG hU. refinementNumbering bijects the finer Parts with the dependent sum over each earlier actual part of its numbered continuations. This proves the row recurrence for the same actual subset, keeping both repeated endpoints and edge multiplicity."))),
                DescribeRole.Theorem))));
}
