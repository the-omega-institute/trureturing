using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut-independent coordinates of actual beams.",
        H("Cut-independent coordinates of actual beams"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("actual-beam-colimit-coordinate"),
                DeclarationHandle.Create(Prefix + "beamCoordinate"),
                H("Select a cut only to define an intrinsic coordinate"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Call("hasType", Call("beamCoordinate", I("G"), I("U")), Call("RowLimit", I("G"))),
                            B("U", Call("Beam", I("G")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("RowLimit G is the existing StationaryModule of rowTransition G = (adjacency G).toLinearMapRight'. hasType displays a definition's result type, not a new proposition. coordinateAt G U n hn is intStage (rowTransition G) n (endpointRow G U n), installing hn.1 as the finite-parts instance. beamCoordinate uses a cut chosen from U.property. With Essential G, coordinateAt_eq removes dependence on that choice and coordinateAt_ray gives intStage n (Pi.single (endpoint alpha n) 1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("all-integer-cuts-coordinate-independence"),
                DeclarationHandle.Create(Prefix + "coordinateAt_eq"),
                H("Two cuts of the same actual beam give the same integer class"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call("coordinateAt", I("G"), I("U"), I("n"), I("hn")),
                                Call("coordinateAt", I("G"), I("U"), I("m"), I("hm"))),
                            B("U", Call("Set", Call("History", I("G")))),
                            B("n", I("Int")),
                            B("m", I("Int")),
                            B("hn", Call("AtCut", I("G"), I("U"), I("n"))),
                            B("hm", Call("AtCut", I("G"), I("U"), I("m")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Both intrinsic partitions refine to max n m, with natural lengths (max n m-n).toNat and (max n m-m).toNat. endpointRow_refine and intStage_refine identify their coordinates. Negative cuts and equal ray sets arising from unique continuation remain in scope; no cut is identified by an inverse transition."))),
                DescribeRole.Theorem))));
}
