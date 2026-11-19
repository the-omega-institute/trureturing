using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class BasedJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure/BasedJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cone collapse is rebased at a native vertex while its quotient map remains unchanged. Exact collapsed-cone traces give relative inverse homotopies and assemble the two-component, common-vertex, and finite-family join decompositions.",
        H("BasedJoin"),
        Blocks(
            Paragraph(Text("A cone collapse is rebased at a native vertex while its quotient map remains unchanged. Exact collapsed-cone traces give relative inverse homotopies and assemble the two-component, common-vertex, and finite-family join decompositions.")),
            Node("based-trans", "basedTrans", "Composition of based equivalences",
                "For topological spaces X,Y,Z, points x:X,y:Y,z:Z, and E:SingletonRetractionBasedInverse.BasedEquivalence x y and F:SingletonRetractionBasedInverse.BasedEquivalence y z, basedTrans E F has continuous forward map F.forward.comp E.forward and backward map E.backward.comp F.backward. These send x to z and z to x. The backward-forward composite is homotopic to id X relative to {x}, and the forward-backward composite to id Z relative to {z}. The left homotopy precomposes F.left by E.forward, postcomposes by E.backward, then concatenates E.left; the right homotopy precomposes E.right by F.backward, postcomposes by F.forward, then concatenates F.right."),
            Node("based-homeomorphism", "basedHomeomorphism", "A homeomorphism preserving the chosen point",
                "For topological spaces X,Y, e:X ≃ₜ Y, x:X, y:Y, and h:e x = y, basedHomeomorphism e x y h is a SingletonRetractionBasedInverse.BasedEquivalence x y. Its continuous maps are e and e.symm, with point laws e x = y and e.symm y = x. Its inverse homotopies are the constant identity homotopies, cast along the homeomorphism inverse equations, relative to {x} and {y}."),
            Node("bool-two-point-homeomorph", "boolTwoPointHomeomorph", "Bool as the two coordinate vertices",
                "boolTwoPointHomeomorph : Bool ≃ₜ FiniteSimplicialJoin.Space twoPoints sends b to the vertex with coordinate function Pi.single b 1, where twoPoints is the complex on Bool whose faces have cardinality one. Its inverse returns the unique vertex label, so the vertices at false and true return false and true respectively. The discrete topology on Bool makes this bijection continuous; compactness of Bool and the Hausdorff realization give a homeomorphism."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
