using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetFullStandardBeamRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full original geometric representation realizes id plus Theta exactly for even q.",
        H("The full original geometric representation realizes id plus Theta exactly for even q"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("original-integer-group-full-geometric-rho"),
                DeclarationHandle.Create(Prefix + "rho"),
                H("Conjugate actual whole-set pushforward onto the original integer group"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call(
                            "MonoidHom",
                            Call("ResetFullAut", I("q")),
                            Call(
                                "IntLinearEquiv",
                                Call("DimensionGroup", Call("resetMatrix", I("q"))),
                                Call("DimensionGroup", Call("resetMatrix", I("q"))))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("NatPositive(q)=0<q. ResetGraph q=expandedGraph(resetMatrix q), with the original numbered edges, absolute Sign=Multiplicative Bool anchor, and native discrete product/subtype topology. ResetFullAut q is EVERY history homeomorphism commuting with the original unit shift. Its membership has no assumed window, endpoint preservation or beam-action field.")),
                    Paragraph(Text("nativeEquiv q hq composes the additive equivalences of beamRowEquiv and resetRowLimitEquiv, then uses Mathlib toIntLinearEquiv to express the same coordinate functions with the original native integer-module instance. beamRowEquiv is the equivalence whose maps F and J satisfy BOTH inverse identities for the actual Mathlib Grothendieck completion. resetRowLimitEquiv uses actual numbered adjacency and the two-sign coefficient transport to the original DimensionGroup(resetMatrix q).")),
                    Paragraph(Text("The displayed MonoidHom is rho's exact result type. rho(h) is nativeEquiv composed with resetFullBeamRepresentation(h) and nativeEquiv inverse. The geometric action is whole Set.image, with quotient compatibility proved by conjugated parallel past splices. Functoriality and inverse use the actual homeomorphism composition and inverse. The group remains the original integral stationary colimit at its original right-row orientation; no sign sector or scalar model is substituted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-rho-original-unit-shift"),
                DeclarationHandle.Create(Prefix + "rho_unitShift"),
                H("The original unit left shift has image true Theta"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "linearMap",
                                Apply(
                                    Call("rho", I("q"), I("hq")),
                                    Call("unitShift", Call("ResetGraph", I("q"))))),
                            Call("resetTheta", I("q"))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("linearMap is the underlying e.toLinearMap of an Int-linear equivalence; endSum is addition of linear maps and linearIdentity is LinearMap.id. The actual shift is x_t -> x_(t+1). shift_ray sends the full cut-n ray onto the cut-(n-1) ray with the same endpoint. intStage_shift, including negative cut -1 from original stage zero, gives true resetTheta. The original native vertex basis and the direct-limit existence of a stage representative extend the equality to the entire DimensionGroup; native_hom_ext implements that argument with the original integer-module instance.")),
                    Paragraph(Text("Complement is represented separately by the left action groupAction(resetMatrix q) tau. Complement changes the absolute sign while retaining the XOR label, suffix and edge number. It is distinct as a construction from time transition Theta, even though the two actual maps coincide for the deterministic one-suffix q=1 dynamics."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-full-original-dimension-action"),
                DeclarationHandle.Create(Prefix + "rho_even"),
                H("Every positive even q realizes id plus Theta on the entire original group"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "linearMap",
                                Apply(Call("rho", I("q"), I("hq")), Call("evenAut", I("q"), I("hq"), I("he")))),
                            Call(
                                "endSum",
                                Call("linearIdentity", Call("DimensionGroup", Call("resetMatrix", I("q")))),
                                Call("resetTheta", I("q")))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q"))),
                        B("he", Call("Even", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The witness evenAut is built from the actual resetNumberedData and resetFiniteForgetting, and reset_generic_H_eq_applyTable identifies its generic H with the original finite forward table. The same-cut theorem supplies every numbered outgoing edge of C=1+resetMatrix as a disjoint whole-ray component, with arbitrary legal futures and the correct target endpoint.")),
                    Paragraph(Text("On every original natural-stage vertex basis generator the actual image row is its basis row times expansionMatrix(1+A). Full coefficient transport gives transition(1+A)=id+transition(A). rho_even_basis computes this at every stage; the original vertex basis and direct-limit existence of a stage representative give the displayed equality on the ENTIRE original integer group. All positive Even q, including q=2, are included. No freely chosen algebraic End is installed as the action."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-positive-original-full-iff-even"),
                DeclarationHandle.Create(Prefix + "reset_full_standard_representation_iff"),
                H("Exact membership for every positive q"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Iff(
                            Exists(
                                Equal(
                                    Call("linearMap", Apply(Call("rho", I("q"), I("hq")), I("h"))),
                                    Call(
                                        "endSum",
                                        Call(
                                            "linearIdentity",
                                            Call("DimensionGroup", Call("resetMatrix", I("q")))),
                                        Call("resetTheta", I("q")))),
                                B("h", Call("ResetFullAut", I("q")))),
                            Call("Even", I("q"))),
                        B("q", I("Nat")),
                        B("hq", Call("NatPositive", I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The formula is exactly forall q:Nat, forall hq:0<q, (exists h:ResetFullAut q, (rho q hq h).toLinearMap=LinearMap.id+resetTheta q) iff Even q. The existential ranges over the full group of actual unit-shift-commuting history homeomorphisms, using the same original DimensionGroup and original unit shift.")),
                    Paragraph(Text("The even direction supplies evenAut and rho_even. If q is odd, including q=1, the explicit integral row w_i=(-1)^i(single 1 1-single tau 1) satisfies T w=-w and has coefficient (-1)^k at suffix zero after every future iterate. Its true original stage-zero colimit class survives and is killed by id+Theta. rho_odd_excluded applies reset_odd_killed_class directly: equality of rho(h).toLinearMap with id+resetTheta would give the nonzero killed class and zero equal images, contradicting rho(h).injective. This obstruction uses no transition-injectivity or torsion-free hypothesis.")),
                    Paragraph(Text("Finite tagged actual beam copies cover the deterministic q=1 graph without an entropy premise. The literal-bit/reset-path coding uses the existing fallback p=1/2 there; the literature's q>=2 positive-entropy regime is not extended to q=1. The statement concerns this geometric integral representation and parity membership. It makes no claim of novelty, an entropy formula, a numerical application, an ordered-cone classification or an additional model theorem."))),
                DescribeRole.Theorem))));
}
