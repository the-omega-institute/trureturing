using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class OriginalDProjectiveSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A modular dihedral representation separates conjugation freeness from a trivial subgroup action.",
        H("Original-D modular projectivity counterexample"),
        Blocks(Describe.Lean(DescribeId.Create("original-d-modular-sharpness"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.originalD_counterexample"),
            H("Nonprojectivity with full original-D hypotheses over F7"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("This is the classical two-dimensional dihedral construction over the field F7. Let G be the dihedral group with 42 elements and N its cyclic rotation subgroup of order 21. Send one rotation to A = diag(2,4), and one reflection to the coordinate exchange S. The identities A cubed equals the identity, S squared equals the identity, and SAS equals the inverse of A define an action factoring through the dihedral group with six elements. For the convention sr(i) = s times r to the i, its matrix is S times A to the i; reversing this order changes the reflection matrices.")),
            Paragraph(Text("Every element outside N is a reflection, and conjugates each rotation to its inverse. A fixed rotation therefore has square equal to the identity. Since N has odd order 21, that rotation is the identity. This is precisely the original condition quantified over all g outside N and all n in N; it is not restricted to a chosen complement or to a chosen generator.")),
            Paragraph(Text("For irreducibility, let W be a nonzero invariant subspace and choose a nonzero vector (x,y) in W. Applying S when necessary makes x nonzero. Applying A minus four times the identity gives (5x,0). Division by 5x puts the first coordinate vector in W, and S puts the second coordinate vector in W. Hence W is the full space. The rotation restriction is nontrivial because A moves the first coordinate vector. This proof uses only the two distinct eigenvalues and the exchange of the coordinate axes; it does not use Maschke's theorem, an algebraic closure, or invertibility of the group order.")),
            Paragraph(Text("The tag-preserving projection from G to the dihedral group with six elements reduces rotation coordinates modulo three. Its kernel H consists of the seven rotations with coordinates divisible by three. The representation factors through this projection, so H acts trivially. H has order seven, while the Frobenius rotation subgroup N has order 21: these are different roles and different subgroups.")),
            Paragraph(Text("The mathematical distinction exposed here is between conjugation on N and the linear action on the representation space. Conjugation is fixed-point-free outside N, yet a subgroup of characteristic order acts trivially on an irreducible representation whose restriction to N is nontrivial.")),
            Paragraph(Text("To prove nonprojectivity of the actual full group-algebra module, suppose it were projective and restrict to H. Mathlib's categorical restriction functor preserves projective objects; its equivalence between representations and group-algebra modules identifies the exact module in this example. The first-coordinate functional is an H-equivariant map to the trivial one-dimensional representation. Projectivity lifts this functional through augmentation from the left regular representation. Evaluate the lift at the first coordinate vector to obtain z in F7[H]. Since H fixes that vector, H fixes z under left translation. Evaluating the coefficient of h in h times z shows that every coefficient equals the coefficient of the identity. Augmentation is therefore seven times that coefficient, which is zero in F7, whereas the lifting identity makes it one. This contradiction proves nonprojectivity, with no assumed homological premise.")),
            Paragraph(Text("The full rotation order is 21, whose image in F7 is zero and hence not a unit. Thus OriginalDFrobenius.projective_originalD, the sufficient theorem in OriginalDProjective, cannot simply drop its invertibility assumption. Conjugation freeness and regular complement data do not prevent a characteristic-order subgroup from being invisible to the representation. This single counterexample gives an existential limit on that sufficient theorem; it does not assert that invertibility of the order of N is universally necessary. The example and the augmentation argument are classical, without a literature novelty claim."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = F.Id("k"), g = F.Id("G"), v = F.Id("V"), n = F.Id("N"), h = F.Id("H");
        Formula rho = F.Id("rho"), z = F.Id("g"), x = F.Id("n");
        Formula Restriction(Formula subgroup) =>
            App(Q("MonoidHom", "comp"), rho, App(Q("Subgroup", "subtype"), subgroup));
        Formula module = App(Q("Representation", "asModule"), rho);
        Formula algebra = App(F.Id("MonoidAlgebra"), k, g);
        Formula cast = Seq(Open, App(Q("Nat", "card"), n), Sp, Colon, Sp, k, Close);
        Formula result = Not(App(Q("Module", "Projective"), algebra, module));
        result = And(Not(App(F.Id("IsUnit"), cast)), result);
        result = And(Eq(App(Q("Nat", "card"), n), D(2, 1)), result);
        result = And(App(Q("Representation", "IsTrivial"), Restriction(h)), result);
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
