using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardTaggedBeamsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric matching of finite tagged actual beams.",
        H("Geometric matching of finite tagged actual beams"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("finite-tagged-actual-beams"),
                DeclarationHandle.Create(Prefix + "Object"),
                H("Finite tags retain identical copies"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("recordType", Call("Object", I("G"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("recordType denotes the Lean structure being described. Object G has Tag : Type v, finiteTag : Finite Tag, and beam : Tag -> Beam G. Its pieces at n are the dependent sum of each tag and Parts of that tag's actual subset. plus uses disjoint sum of tags, not overlapping set union. Thus two identical copies remain two copies. This makes repeated vertex generators available even for a deterministic graph such as reset q=1, where extra disjoint pasts cannot be presumed. No positive-entropy premise is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("geometric-common-cut-matching"),
                DeclarationHandle.Create(Prefix + "Matching"),
                H("Define equivalence by endpoint-preserving geometric matching"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Call("recordType", Call("Matching", I("G"), I("A"), I("Bobj"), I("n"))),
                            B("A", Call("Object", I("G"))),
                            B("Bobj", Call("Object", I("G"))),
                            B("n", I("Int"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Matching G A B n contains left : Normalized G A n, right : Normalized G B n, pieces : Pieces G A n equiv Pieces G B n, and endpoints : forall P, pieceEndpoint(pieces P)=pieceEndpoint P. Normalized says every tagged subset satisfies AtCut at that same integer n. Equivalent G A B is the existence of n with Nonempty (Matching G A B n). Each matched pair is realized by the actual future-preserving spliceEquiv on its two ray subsets. Matching.rows derives row equality. matchingOfRows proves the converse by bijecting finite endpoint fibers; row equality is not the definition of the relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eventual-geometric-matching-coordinate-criterion"),
                DeclarationHandle.Create(Prefix + "equivalent_iff_value_eq"),
                H("Coordinate equality is equivalent to actual eventual matching"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Iff(
                                Call("Equivalent", I("G"), I("A"), I("Bobj")),
                                Equal(
                                    Call("objectValue", I("G"), I("A")),
                                    Call("objectValue", I("G"), I("Bobj")))),
                            B("A", Call("Object", I("G"))),
                            B("Bobj", Call("Object", I("G")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("objectValue G A is the finite sum of beamCoordinate over every tag. The forward direction uses the actual geometric Matching. For the converse, normalize both objects at a common integer cut, advance to a nonnegative stage, and use Module.DirectLimit.exists_eq_of_of_eq to obtain a later stage of equal rows. Numbered refinement produces those rows; matchingOfRows constructs the endpoint-fiber bijection and its past splices. equivalent_iff_common_rows gives the corresponding eventual common-integer-cut criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mathlib-integer-beam-completion"),
                DeclarationHandle.Create(Prefix + "BeamGroup"),
                H("Use the real Grothendieck group of the tagged quotient"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Call("typeAlias", Call("BeamGroup", I("G"), I("hG"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("typeAlias displays the Lean abbreviation. BeamMonoid G hG is Quotient (beamSetoid G hG), with addition induced by plus. BeamGroup G hG is Additive (Algebra.GrothendieckGroup (Multiplicative (BeamMonoid G hG))). intoGroup is the library completion map. F : BeamGroup G hG ->+ RowLimit G extends quotientValue by the actual Mathlib universal property. StandardBeamIdentification constructs J and proves both inverse identities. For a finite DISJOINT same-cut ray union, disjointUnion_group identifies its singleton class with the tagged family of components; this additivity formula is not asserted for an overlapping union."))),
                DescribeRole.Definition))));
}
