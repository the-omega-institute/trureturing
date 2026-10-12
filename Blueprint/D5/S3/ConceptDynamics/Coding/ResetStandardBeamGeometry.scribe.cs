using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetStandardBeamGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete even whole-ray images and their original native coordinates.",
        H("Concrete even whole-ray images and their original native coordinates"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("concrete-even-full-automorphism"),
                DeclarationHandle.Create(Prefix + "evenAut"),
                H("The actual alternating construction belongs to the full domain"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("hasType", Call("evenAut", I("q"), I("hq"), I("he")), Call("ResetFullAut", I("q"))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("he", Call("Even", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("NatPositive(q) means 0<q. ResetGraph q=expandedGraph(resetMatrix q), ResetHistory q=History(ResetGraph q), and ResetFullAut q=FullAut(ResetGraph q). The actual finite expanded vertices and numbered edges use their native discrete topologies. Alternating.reset_expanded_essential q hq supplies both edge directions for every positive q, including deterministic q=1.")),
                    Paragraph(Text("evenAut q hq he uses resetAlternatingWholeRayHomeomorph from actual NumberedData with C=1+resetMatrix and the proved resetFiniteForgetting. reset_generic_H_eq_applyTable identifies it with the original forward table on every history, whose shift law proves membership. Positive Even q includes q=2 and never requires q>=3. hasType displays the definition's result type."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-numbered-whole-image-row"),
                DeclarationHandle.Create(Prefix + "even_image_endpointRow"),
                H("At the unchanged cut, every numbered edge of 1+A contributes"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "endpointRow",
                                Call("ResetGraph", I("q")),
                                Call(
                                    "image",
                                    Call("homeomorph", Call("evenAut", I("q"), I("hq"), I("he"))),
                                    Call("ray", Call("ResetGraph", I("q")), I("alpha"), I("n"))),
                                I("n")),
                            Call(
                                "rightMultiply",
                                Call("singleEndpoint", Call("ResetGraph", I("q")), I("alpha"), I("n")),
                                Call("expansionMatrix", Call("matrixOneAdd", Call("resetMatrix", I("q")))))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("he", Call("Even", I("q"))),
                        B("alpha", Call("History", Call("ResetGraph", I("q")))),
                        B("n", I("Int"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("singleEndpoint is Pi.single (endpoint (ResetGraph q) alpha n) 1. matrixOneAdd(A) is (1 : GroupMat Sign q q)+A. endpointRow installs the Finite Parts instance derived by even_image_atCut. reset_even_same_cut_whole_rays decomposes the actual image into whole, pairwise disjoint rays indexed by full numbered outgoing C edges, each with the target of its own indexing edge. endpointRow_disjointUnion sums each contribution, and expandedEdgeFiberEquiv counts the actual edge numbers to identify adjacency with expansionMatrix. Thus multiplicity, source, target and absolute sign are all retained."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-shift-at-every-integer-cut"),
                DeclarationHandle.Create(Prefix + "reset_actual_shift_ray_coordinate"),
                H("The true ray shift induces true Theta, including negative cuts"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "resetBeamCoordinate",
                                I("q"),
                                Call("shiftImageRayBeam", I("q"), I("hq"), I("alpha"), I("n"))),
                            Apply(
                                Call("Theta", Call("transition", Call("resetMatrix", I("q")))),
                                Call(
                                    "resetBeamCoordinate",
                                    I("q"),
                                    Call("resetRayBeam", I("q"), I("hq"), I("alpha"), I("n"))))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("alpha", Call("History", Call("ResetGraph", I("q")))),
                        B("n", I("Int"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("shiftImageRayBeam is the Beam whose actual set is shift (ResetGraph q) image of ray alpha n, with the AtCut witness at n-1 supplied by shift_ray. resetBeamCoordinate is beamCoordinate followed by resetRowLimitEquiv. That equivalence first uses equality of the graph's counted adjacency with expansionMatrix, then the full two-coefficient NativeIntegralRowTransport.limitEquiv.")),
                    Paragraph(Text("An actual ray at ANY integer cut has coordinate intStage (transition(resetMatrix q)) n (vertex endpointSuffix endpointSign). shift_ray preserves that endpoint and sends n to n-1; intStage_shift gives the equality. Theta is induced by the row transition. The separate left group action groupAction(resetMatrix q) tau represents complement, not this construction of time shift."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("concrete-even-geometric-native-stage-action"),
                DeclarationHandle.Create(Prefix + "reset_fullBeam_even_stage"),
                H("The actual even image gives id plus Theta at every original ray stage"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Apply(
                                Call("resetRowLimitEquiv", I("q")),
                                Apply(
                                    Call(
                                        "F",
                                        Call("ResetGraph", I("q")),
                                        Call("resetEssential", I("q"), I("hq"))),
                                    Apply(
                                        Call(
                                            "resetFullBeamRepresentation",
                                            I("q"),
                                            I("hq"),
                                            Call("evenAut", I("q"), I("hq"), I("he"))),
                                        Call(
                                            "objectGroup",
                                            Call("ResetGraph", I("q")),
                                            Call("resetEssential", I("q"), I("hq")),
                                            Call(
                                                "singleton",
                                                Call("ResetGraph", I("q")),
                                                Call(
                                                    "resetRayBeam",
                                                    I("q"),
                                                    I("hq"),
                                                    I("alpha"),
                                                    Call("intCast", I("N")))))))),
                            Apply(
                                Call(
                                    "endSum",
                                    Call("linearIdentity", Call("DimensionGroup", Call("resetMatrix", I("q")))),
                                    Call("Theta", Call("transition", Call("resetMatrix", I("q"))))),
                                Apply(
                                    Call("stage", Call("transition", Call("resetMatrix", I("q"))), I("N")),
                                    Call(
                                        "vertexOfPair",
                                        Call(
                                            "endpoint",
                                            Call("ResetGraph", I("q")),
                                            I("alpha"),
                                            Call("intCast", I("N"))))))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("he", Call("Even", I("q"))),
                        B("alpha", Call("History", Call("ResetGraph", I("q")))),
                        B("N", I("Nat"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("resetEssential(q,hq) abbreviates Alternating.reset_expanded_essential q hq, vertexOfPair(p)=vertex p.1 p.2, intCast is the natural-to-integer coercion, and endSum is addition of Int-linear maps. The stage map is the original Module.DirectLimit.of.")),
                    Paragraph(Text("The same-cut disjoint whole-ray theorem is consumed by even_image_tagged_group to equate the actual image singleton with its tagged numbered components. F evaluates those components, resetRowLimitEquiv transports their original stage, and native_transition_one_add computes transition(1+A) z=z+transition(A) z on the FULL Int[C2] row. This proves the actual fullBeam action formula, not a formula for an arbitrary End assigned the name rho. The whole-group conclusion is established in the owning root module."))),
                DescribeRole.Theorem))));
}
