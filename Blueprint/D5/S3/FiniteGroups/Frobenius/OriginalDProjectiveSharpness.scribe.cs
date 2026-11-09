using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDProjectiveSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A modular dihedral representation separates conjugation freeness from a trivial subgroup action.",
        H("Original-D modular sharpness data"),
        Blocks(Describe.Lean(DescribeId.Create("original-d-modular-sharpness-data"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.originalD_example_data"),
            H("Full original-D data over F7"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("This is the classical two-dimensional dihedral construction over the field F7. Let G be the dihedral group with 42 elements and N its cyclic rotation subgroup of order 21. Send one rotation to A = diag(2,4), and one reflection to the coordinate exchange S. The identities A cubed equals the identity, S squared equals the identity, and SAS equals the inverse of A define an action factoring through the dihedral group with six elements. For the convention sr(i) = s times r to the i, its matrix is S times A to the i; reversing this order changes the reflection matrices.")),
            Paragraph(Text("Every element outside N is a reflection, and conjugates each rotation to its inverse. A fixed rotation therefore has square equal to the identity. Since N has odd order 21, that rotation is the identity. This is precisely the original condition quantified over all g outside N and all n in N; it is not restricted to a chosen complement or to a chosen generator.")),
            Paragraph(Text("For irreducibility, let W be a nonzero invariant subspace and choose a nonzero vector (x,y) in W. Applying S when necessary makes x nonzero. Applying A minus four times the identity gives (5x,0). Division by 5x puts the first coordinate vector in W, and S puts the second coordinate vector in W. Hence W is the full space. The rotation restriction is nontrivial because A moves the first coordinate vector. This proof uses only the two distinct eigenvalues and the exchange of the coordinate axes; it does not use Maschke's theorem, an algebraic closure, or invertibility of the group order.")),
            Paragraph(Text("The tag-preserving projection from G to the dihedral group with six elements reduces rotation coordinates modulo three. Its kernel H consists of the seven rotations with coordinates divisible by three. The representation factors through this projection, so H acts trivially. H has order seven, while the Frobenius rotation subgroup N has order 21: these are different roles and different subgroups.")),
            Paragraph(Text("The mathematical distinction exposed here is between conjugation on N and the linear action on the representation space. Conjugation is fixed-point-free outside N, yet a subgroup of characteristic order acts trivially on an irreducible representation whose restriction to N is nontrivial. The order-seven subgroup supplies the concrete input for a separate projectivity obstruction over the group algebra. The combined data statement does not itself contain that homological conclusion. The example and its coordinate proof are classical, without a literature novelty claim."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = F.Id("k"), g = F.Id("G"), v = F.Id("V"), n = F.Id("N"), h = F.Id("H");
        Formula rho = F.Id("rho"), z = F.Id("g"), x = F.Id("n");
        Formula Restriction(Formula subgroup) =>
            App(Q("MonoidHom", "comp"), rho, App(Q("Subgroup", "subtype"), subgroup));
        Formula result = App(Q("Representation", "IsTrivial"), Restriction(h));
        result = And(Eq(App(Q("Nat", "card"), h), D(7)), result);
        result = And(App(F.Id("Finite"), h), result);
        result = And(Not(App(Q("Representation", "IsTrivial"), Restriction(n))), result);
        Formula fixedFree = All("g", g, Imp(Not(App(Q("Membership", "mem"), n, z)),
            All("n", n, Imp(Eq(App(App(Q("MulAut", "conjNormal"), z), x), x), Eq(x, D(1))))));
        result = And(fixedFree, result);
        result = And(App(Q("Subgroup", "Normal"), n), result);
        result = And(App(Q("Representation", "IsIrreducible"), rho), result);
        result = And(App(F.Id("FiniteDimensional"), k, v), result);
        result = And(Eq(App(Q("Nat", "card"), g), D(4, 2)), result);
        return And(App(F.Id("Finite"), g), result);
    }

    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Not(Formula p) => Seq(Neg, Sp, Open, p, Close);
}
