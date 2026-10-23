using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual integer-cut rays and intrinsic finite beams.",
        H("Actual integer-cut rays and intrinsic finite beams"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("integer-cut-full-ray"),
                DeclarationHandle.Create(Prefix + "ray"),
                H("The whole fixed past at any integer cut"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Iff(
                                Member(I("x"), Call("ray", I("G"), I("alpha"), I("n"))),
                                Forall(
                                    Imp(
                                        Le(I("k"), I("n")),
                                        Equal(
                                            Call("coordinate", I("x"), I("k")),
                                            Call("coordinate", I("alpha"), I("k")))),
                                    B("k", I("Int")))),
                            B("alpha", Call("History", I("G"))),
                            B("n", I("Int")),
                            B("x", Call("History", I("G")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("ray G alpha n is the actual subset fixing every edge k<=n, including arbitrarily negative k. Its endpoint is G.target(alpha n). Rays at a fixed cut are disjoint or equal as sets. RayAt stores those actual sets, so equality removes a repeated past rather than merely a repeated endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("future-preserving-past-splice"),
                DeclarationHandle.Create(Prefix + "spliceEquiv"),
                H("Replace an entire past and keep every future edge"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Call(
                                "Equiv",
                                Call("ray", I("G"), I("alpha"), I("n")),
                                Call("ray", I("G"), I("beta"), I("n"))),
                            B("alpha", Call("History", I("G"))),
                            B("beta", Call("History", I("G"))),
                            B("n", I("Int")),
                            B(
                                "ep",
                                Equal(
                                    Call("endpoint", I("G"), I("alpha"), I("n")),
                                    Call("endpoint", I("G"), I("beta"), I("n"))))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Equiv denotes Lean Equiv between the two ray subtypes. spliceEquiv uses beta k for k<=n and the supplied ray member x k for k>n. Equality of the two target endpoints is precisely the seam hypothesis. Replacing the past back proves both inverse identities; no future is selected or restricted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("numbered-continuation-full-refinement"),
                DeclarationHandle.Create(Prefix + "ray_refine"),
                H("All numbered continuations partition the full ray"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call("ray", I("G"), I("alpha"), I("n")),
                                Call("refinedRayUnion", I("G"), I("hG"), I("alpha"), I("n"), I("r"))),
                            B("alpha", Call("History", I("G"))),
                            B("n", I("Int")),
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
                    Paragraph(Text("refinedRayUnion is the indexed union over p : Continuation G (endpoint G alpha n) r of ray G (refined G hG alpha n r p) (n+(r:Int)). Continuation is PUnit at length zero and a dependent pair of an actual outgoing edge and a continuation at its target at successor length. Every edge, including its parallel-edge number, is retained. ray_refine_disjoint gives disjointness for unequal continuation indices; refined_endpoint is continuationEnd p. The finite cardinality is at most Delta G raised to r, where Delta is max 1 of the maximal outgoing degree. These are arbitrary natural lengths and integer cuts."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("intrinsic-finite-beam"),
                DeclarationHandle.Create(Prefix + "IsBeam"),
                H("Finite saturated partitions of actual subsets"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Iff(
                                Call("IsBeam", I("G"), I("U")),
                                Exists(Call("AtCut", I("G"), I("U"), I("n")), B("n", I("Int")))),
                            B("U", Call("Set", Call("History", I("G"))))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Parts G U n is {P : RayAt G n // P.val is a subset of U}. AtCut G U n means Finite (Parts G U n) AND every x in U has its entire ray G x n contained in U. Beam G is the subtype of IsBeam subsets. The finite condition alone would allow selected points and would not supply the required saturation.")),
                    Paragraph(Text("Under finite vertex/edge instances, DecidableEq V and Essential G, parts_union and parts_disjoint give the intrinsic disjoint partition. atCut_mono refines it to any later integer cut. Finite unions normalize equal actual ray sets, while distinct rays with coincident endpoints remain separate. If the same ray set occurs at two ordered cuts, equal_ray_unique_continuation proves its numbered refinement has exactly one component."))),
                DescribeRole.Definition))));
}
