using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SurfaceObservers;

internal sealed class NormalSubdirectInnerActionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Scott = LibraryNoteRef.Create("D5/L/FiniteGroups/neunen2016subdirect");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal subdirect products of nonabelian simple groups are rigid and their extension actions are inner.",
        H("Normal subdirect rigidity and common inner action"),
        Blocks(
            Describe.Lean(DescribeId.Create("normal-subdirect-finite-observer-rigidity"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SurfaceObservers/NormalSubdirectInnerAction.finite_observer_rigidity"),
                H("Normal subdirect rigidity"), StatementSource.FromAuthor(FiniteRigidity()),
                AssessedProvenance.FromLiterature(Scott),
                Blocks(Paragraph(Text("For a finite coordinate family of noncommutative simple groups, a jointly injective family of coordinate surjections has no proper normal subgroup mapping onto every factor. The proof absorbs the joint kernel by a common commutator lift."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("subdirect-perfect"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SurfaceObservers/NormalSubdirectInnerAction.subdirect_perfect"),
                H("A subdirect product is perfect"), StatementSource.FromAuthor(Perfect()),
                AssessedProvenance.FromLiterature(Scott),
                Blocks(Paragraph(Text("Under the same hypotheses, the commutator subgroup of the source group is the whole source group."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normal-joint-range"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SurfaceObservers/NormalSubdirectInnerAction.normal_joint_range"),
                H("The normal joint image is the ambient joint image"), StatementSource.FromAuthor(JointRange()),
                AssessedProvenance.FromLiterature(Scott),
                Blocks(Paragraph(Text("A normal subgroup mapping onto every coordinate has the same joint image as the ambient group."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-inner-action"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SurfaceObservers/NormalSubdirectInnerAction.common_inner_action"),
                H("A single normal element realizes every coordinate action"), StatementSource.FromAuthor(CommonAction()),
                AssessedProvenance.FromLiterature(Scott),
                Blocks(Paragraph(Text("For each ambient element there is one normal element whose coordinate images agree with it. Conjugation by the two elements agrees in every coordinate, and the corresponding outer class is the identity."))), DescribeRole.Theorem),
            Paragraph(Text("This is the classical normal-subdirect-product phenomenon, often called Scott's lemma in finite-group literature. The formal development makes the common commutator lift explicit and claims no new literature result.")))));

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, params Formula[] rest) { Formula r = a; foreach (var x in rest) r = new Formula.Logic(r, FormulaLogicOperator.And, x); return r; }
    private static Formula ForAll(string name, Formula domain, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Exists(string name, Formula domain, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula FiniteRigidity()
    {
        var i = F.Id("I"); var s = F.Id("S"); var g = F.Id("G"); var m = F.Id("M");
        var factor = And(Call("GroupFamily", s), Call("SimpleFamily", s), Call("NoncommutativeFamily", s));
        var maps = And(Call("JointInjective", F.Id("f")), Call("CoordinateSurjective", F.Id("f")), Call("Normal", m), Call("CoordinateImagesTop", m));
        return Disp(ForAll("I", Call("Typeu"), Implies(Call("Finite", i), ForAll("S", Call("Family", i), Implies(factor, ForAll("G", Call("Typeu"), ForAll("f", Call("CoordinateHom", g, s), ForAll("M", Call("Subgroup", g), Implies(maps, Equal(m, F.Id("TopG"))))))))));
    }
    private static Formula Perfect()
    {
        var i = F.Id("I"); var s = F.Id("S"); var g = F.Id("G");
        return Disp(ForAll("I", Call("Typeu"), Implies(Call("Finite", i), ForAll("S", Call("Family", i), ForAll("G", Call("Typeu"), ForAll("f", Call("CoordinateHom", g, s), Implies(And(Call("GroupFamily", s), Call("SimpleFamily", s), Call("NoncommutativeFamily", s), Call("JointInjective", F.Id("f")), Call("CoordinateSurjective", F.Id("f"))), Equal(Call("commutator", g), F.Id("TopG"))))))));
    }
    private static Formula JointRange()
    {
        var i = F.Id("I"); var s = F.Id("S"); var e = F.Id("E"); var n = F.Id("N");
        return Disp(ForAll("I", Call("Typeu"), Implies(Call("Finite", i), ForAll("S", Call("Family", i), ForAll("E", Call("Typeu"), ForAll("rho", Call("CoordinateHom", e, s), ForAll("N", Call("Subgroup", e), Implies(And(Call("GroupFamily", s), Call("SimpleFamily", s), Call("NoncommutativeFamily", s), Call("Normal", n), Call("CoordinateImagesTop", n)), Equal(Call("jointImage", n, F.Id("rho")), Call("jointImage", e, F.Id("rho"))))))))));
    }
    private static Formula CommonAction()
    {
        var i = F.Id("I"); var s = F.Id("S"); var e = F.Id("E"); var n = F.Id("N");
        var body = Exists("n0", n, And(Call("SameCoordinateImages", F.Id("n0"), F.Id("e")), Call("ConjugationsAgree", F.Id("n0"), F.Id("e"), F.Id("rho")), Call("OuterClassIdentity", F.Id("n0"), F.Id("e"), F.Id("rho"))));
        return Disp(ForAll("I", Call("Typeu"), Implies(Call("Finite", i), ForAll("S", Call("Family", i), ForAll("E", Call("Typeu"), ForAll("rho", Call("CoordinateHom", e, s), ForAll("N", Call("Subgroup", e), Implies(And(Call("GroupFamily", s), Call("SimpleFamily", s), Call("NoncommutativeFamily", s), Call("Normal", n), Call("CoordinateImagesTop", n)), ForAll("e", e, body))))))));
    }
}
