using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamIdentificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both inverses between geometric completion and the original row colimit.",
        H("Both inverses between geometric completion and the original row colimit"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("actual-ray-built-inverse"),
                DeclarationHandle.Create(Prefix + "J"),
                H("Build the inverse from full vertex rays and signed integer sums"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call(
                            "hasType",
                            Call("J", I("G"), I("hG")),
                            Call("IntLinearMap", Call("RowLimit", I("G")), Call("BeamGroup", I("G"), I("hG")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("chosenRay u N is the entire ray at cut (N:Int) of vertexHistory G hG u N. chosenClass is its singleton image in the actual Mathlib completion. JStage N z is the FULL signed integer sum over u:V of z u times chosenClass u N. F_chosenClass identifies each actual generator with stage N (Pi.single u 1), and F_JStage extends to every integral row.")),
                    Paragraph(Text("F_injective is derived from equivalent_iff_value_eq and the localization universal property. It proves JStage_compatible after the actual geometric generator calculation, not from an assumed lift field. The original Module.DirectLimit.lift then constructs J. Auxiliary history choices disappear through endpoint-preserving past splices and matching."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("geometric-native-first-inverse"),
                DeclarationHandle.Create(Prefix + "FJ"),
                H("F followed after J is identity on the whole original row colimit"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "compose",
                                Call("intLinearMap", Call("F", I("G"), I("hG"))),
                                Call("J", I("G"), I("hG"))),
                            Call("linearIdentity", Call("RowLimit", I("G")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("compose is LinearMap.comp; intLinearMap(F) is F.toIntLinearMap. The exact equality is (F G hG).toIntLinearMap.comp (J G hG)=LinearMap.id on RowLimit G. Direct-limit hom_ext reduces it to every natural stage and every signed integer row, where F_JStage gives the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometric-native-second-inverse"),
                DeclarationHandle.Create(Prefix + "JF"),
                H("J followed after F is identity on the actual group completion"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Equal(
                            Call(
                                "compose",
                                Call("J", I("G"), I("hG")),
                                Call("intLinearMap", Call("F", I("G"), I("hG")))),
                            Call("linearIdentity", Call("BeamGroup", I("G"), I("hG")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exact equality is (J G hG).comp (F G hG).toIntLinearMap=LinearMap.id on BeamGroup G hG. Apply the previously derived F_injective to each completion element and then FJ. This handles all formal differences through Mathlib localization. beamRowEquiv is the resulting Int-linear equivalence with forward F and inverse J; neither direction is merely a promised isomorphism."))),
                DescribeRole.Theorem))));
}
