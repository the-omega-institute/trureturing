using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class InfiniteCostShortcutBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-point extended metric separates infinite paid cost from a zero-cost self-gluing shortcut.",
        H("Infinite cost and self-gluing shortcuts"),
        Blocks(
            Paragraph(Text("Use Bool as a two-point extended metric space: equal points have distance zero and distinct points have distance infinity. The first datum has one piece, no generators and the identity family of points. Its chain rules therefore permit a one-step paid move from false to true, but that move has infinite cost.")),
            Paragraph(Text("The second datum has one closed singleton generator with domain {false}, range {true}, and the unique isometry between them. The forward gluing move changes false to true at zero cost. Both data have finite actual orbits, since the ambient tagged point type has only two elements. The statements below are the exact finite-chain consequences used at the boundary of the finite-cost hypothesis.")),
            Describe.Lean(DescribeId.Create("no-generator-distance-infinite"),
                Handle("no_generator_distance_infinite"), H("The no-generator distance is infinite"),
                StatementSource.FromAuthor(F.Disp(Eq(Call("distance", Id("noGeneratorDatum"), Call("point", Id("false")), Call("point", Id("true"))), F.Infty))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The infimum is infinity because every chain from false to true either stays at the same Bool value or has a paid move of cost infinity. An infinite-cost chain can still exist, so this statement concerns the distance value rather than nonexistence of a chain.")))),
            Describe.Lean(DescribeId.Create("no-generator-finite-chain-exists"),
                Handle("no_generator_finite_chain_exists"), H("An infinite-cost finite chain still exists"),
                StatementSource.FromAuthor(F.Disp(Exists("t", Extended, Call("Chain", Id("noGeneratorDatum"), Call("point", Id("false")), Call("point", Id("true")), Id("t"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The witness is the single paid move from false to true. Its cost is edist(false,true)=infinity, so the finite derivation has an extended cost of infinity.")))),
            Describe.Lean(DescribeId.Create("self-glue-distance-zero"),
                Handle("self_glue_distance_zero"), H("Self-gluing makes the distance zero"),
                StatementSource.FromAuthor(F.Disp(Eq(Call("distance", Id("selfGlueDatum"), Call("point", Id("false")), Call("point", Id("true"))), F.D(0)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The closed singleton self-gluing supplies a forward generator step of cost zero. The chain-distance infimum is therefore at most zero and hence equals zero.")))),
            Describe.Lean(DescribeId.Create("self-glue-orbits-finite"),
                Handle("self_glue_orbits_finite"), H("Self-gluing orbits are finite"),
                StatementSource.FromAuthor(F.Disp(All("a", PointType, Call("Finite", Call("O", Id("selfGlueDatum"), Id("a")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The orbit is a subset of the two-point tagged space, so it is finite.")))),
            Describe.Lean(DescribeId.Create("no-generator-orbits-finite"),
                Handle("no_generator_orbits_finite"), H("No-generator orbits are finite"),
                StatementSource.FromAuthor(F.Disp(All("a", PointType, Call("Finite", Call("O", Id("noGeneratorDatum"), Id("a")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The orbit is a subset of the same two-point tagged space, so it is finite even without generators.")))),
            Paragraph(Text("This is a concrete boundary instance. It does not assert a general quotient construction, geodesicity, isometric embedding of the original piece, or any curvature or angle statement. The example records why a finite-cost qualifier is necessary when a chain metric is used to recover an original realization.")))));

    private static Formula PointType => Call("Sigma", new Formula.TypeArrow(Id("Unit"), Id("Bool")));
    private static Formula Extended => Id("ENNReal");
    private static DeclarationHandle Handle(string selector) =>
        DeclarationHandle.Create("D5/S3/Topology/InfiniteCostShortcutBoundary." + selector);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Exists(string s, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
