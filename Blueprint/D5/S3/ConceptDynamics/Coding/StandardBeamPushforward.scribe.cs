using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamPushforwardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Functorial whole-set image on the actual geometric completion.",
        H("Functorial whole-set image on the actual geometric completion"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("actual-set-image-keeps-every-tag"),
                DeclarationHandle.Create(Prefix + "imageObject"),
                H("Push each entire beam through the actual homeomorphism"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Call(
                                "hasType",
                                Call("imageObject", I("G"), I("hG"), I("h"), I("A")),
                                Call("Object", I("G"))),
                            B("h", Call("FullAut", I("G"))),
                            B("A", Call("Object", I("G")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("imageObject keeps A.Tag and A.finiteTag, and sends beam i to imageBeam G hG h (A.beam i), whose set is h.val image of the WHOLE beam. hasType displays the definition's type. Image sets are beams by the compactness-derived window theorem. Tags retain identical copies. The intrinsic disjoint partition of a beam maps to a disjoint family because the actual h is injective. Coordinates add for these disjoint unions at a common cut."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-domain-geometric-quotient-compatibility"),
                DeclarationHandle.Create(Prefix + "imageObject_equivalent"),
                H("Actual image respects every geometric equivalence"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Call(
                                "Equivalent",
                                I("G"),
                                Call("imageObject", I("G"), I("hG"), I("h"), I("A")),
                                Call("imageObject", I("G"), I("hG"), I("h"), I("Bobj"))),
                            B("h", Call("FullAut", I("G"))),
                            B("A", Call("Object", I("G"))),
                            B("Bobj", Call("Object", I("G"))),
                            B("he", Call("Equivalent", I("G"), I("A"), I("Bobj")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An original common-cut Matching pairs actual ray pieces with equal endpoints. For each pair, parallel_image_coordinate uses conjugatePartsEquiv at n+a+b+d, whose individual restrictions are actual future-preserving splices. imageObject_value_partition sums these coordinates over every original tagged piece. Their equality and equivalent_iff_value_eq produce an actual eventual Matching of the images. No algebraic action, beam-image promise, colimit isomorphism or supplied window is a premise."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-covariant-integer-beam-representation"),
                DeclarationHandle.Create(Prefix + "fullBeamRepresentation"),
                H("Functorial image gives an integral representation with the actual inverse"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call(
                            "MonoidHom",
                            Call("FullAut", I("G")),
                            Call(
                                "IntLinearEquiv",
                                Call("BeamGroup", I("G"), I("hG")),
                                Call("BeamGroup", I("G"), I("hG")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The displayed MonoidHom is the result type of fullBeamRepresentation G hG. monoidImage descends imageObject to the geometric quotient. groupImage extends intoGroup composed with monoidImage by the Mathlib Grothendieck universal property. Set.image composition gives groupImage(g*h)=groupImage(g) composed with groupImage(h), and identity maps to identity.")),
                    Paragraph(Text("groupImageEquiv uses groupImage(h inverse) as its inverse; both inverse laws follow from these composition identities and the actual homeomorphism inverse. Converting the additive equivalence to an Int-linear equivalence produces fullBeamRepresentation. On every original object generator its action is objectGroup(imageObject h A). This is a representation on the completed geometric integer group; identifying it with the native row group uses both identities in StandardBeamIdentification."))),
                DescribeRole.Definition))));
}
