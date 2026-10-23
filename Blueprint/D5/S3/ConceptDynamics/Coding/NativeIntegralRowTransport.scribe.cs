using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class NativeIntegralRowTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-sign integer coordinate transport on the original row colimit.",
        H("Two-sign integer coordinate transport on the original row colimit"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("two-sign-integral-basis-equivalence"),
                DeclarationHandle.Create(Prefix + "basisEquiv"),
                H("Retain both C2 coefficients with the original row orientation"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("IntLinearEquiv", Call("ExpandedRow", I("q")), Call("NativeRow", I("q"))),
                        B("q", I("Nat"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Sign is Multiplicative Bool with XOR addition, identity ofAdd false and tau=ofAdd true. ExpandedRow q=(Fin q times Sign)->Int; NativeRow q=VertexModule Sign q=Fin q->MonoidAlgebra Int Sign. basisEquiv sends v to the row i |-> single 1 (v(i,1)) + single tau (v(i,tau)). Its inverse reads every coefficient (z i).coeff h. decode_encode and encode_decode recover both coordinates; no plus/minus quotient, rationalization or integral splitting is used. The formula displays the definition's equivalence type for every natural q."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-right-row-transition-transport"),
                DeclarationHandle.Create(Prefix + "transport_transition"),
                H("Conjugate the actual integer row transition to the native transition"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Apply(Call("basisEquiv", I("q")), Apply(Call("rowTransition", I("M")), I("v"))),
                                Apply(Call("transition", I("M")), Apply(Call("basisEquiv", I("q")), I("v")))),
                            B("v", Call("ExpandedRow", I("q")))),
                        B("q", I("Nat")),
                        B("M", Call("GroupMat", I("Sign"), I("q"), I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("M : GroupMat Sign q q is an arbitrary natural-coefficient group matrix. expansionMatrix M (i,h) (j,t) is the integer cast of (M i j).coeff(h inverse * t). rowTransition M is its toLinearMapRight', the row map v |-> v B, not a transpose. actual_expansion_adjacency on each native vertex basis extends by linearity to every integral row. transport_power and inverse_transport_power give the same intertwining for every natural power."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("same-original-stages-native-colimit-equivalence"),
                DeclarationHandle.Create(Prefix + "limitEquiv"),
                H("Transport every original stage, with both inverse identities"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("IntLinearEquiv", Call("ExpandedLimit", I("M")), Call("DimensionGroup", I("M"))),
                        B("q", I("Nat")),
                        B("M", Call("GroupMat", I("Sign"), I("q"), I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("ExpandedLimit M is StationaryModule(rowTransition M); DimensionGroup M is the existing StationaryModule(transition M). Module.DirectLimit.map of basisEquiv at each natural stage constructs toNativeLimit, and its inverse constructs fromNativeLimit. For every n:Nat and expanded row v, toNativeLimit(stage n v)=native stage n (basisEquiv v); the inverse has the corresponding same-stage formula for every native row. limits_left_inverse and limits_right_inverse yield limitEquiv. This is coefficient transport on the same original integer colimits, not yet a geometric beam action."))),
                DescribeRole.Definition))));
}
