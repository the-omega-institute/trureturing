using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class TorusOrbitClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The closure of the nonnegative powers of any point of a finite torus is determined "
        + "by exactly the integer characters that equal one at that point.",
        H("Integer Characters Determine Torus Orbit Closures"),
        Blocks(Describe.Lean(
            DescribeId.Create("torus-orbit-closure"),
            DeclarationHandle.Create("D5/S3/Fourier/TorusOrbitClosure.result"),
            H("The complete integer relation criterion"),
            StatementSource.FromAuthor(OrbitFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let I be any finite index type. Circle is the multiplicative group of "
                    + "complex numbers of modulus one, and powers of a function are taken "
                    + "coordinatewise. The closure uses the product topology. Natural powers "
                    + "include zero. Every integer vector k is tested, including negative "
                    + "exponents, and the implication retains exactly the relations of g.")),
                Paragraph(Text(
                    "The nonnegative power orbit has the same closure as the integer power "
                    + "orbit. This closure is a compact subgroup G. Continuity of each "
                    + "character proves that its value is one throughout G whenever its "
                    + "value at g is one.")),
                Paragraph(Text(
                    "For the converse, average continuous functions over G using normalized "
                    + "Haar measure, and compare this average with the average over zG. "
                    + "Translation by g forces the integral of a character to vanish unless "
                    + "the character equals one at g. For the remaining characters, the "
                    + "assumed relation makes translation by z leave the integral unchanged. "
                    + "The dense span of the torus characters therefore makes the two "
                    + "continuous linear averaging functionals equal on every continuous "
                    + "complex-valued function. If z were outside G, the compact cosets G "
                    + "and zG would be disjoint. A continuous function equal to zero on G "
                    + "and one on zG would then have both equal and unequal averages, a "
                    + "contradiction.")),
                Paragraph(Text(
                    "No independence or algebraicity condition is imposed on the phases. "
                    + "The empty index type, finite periodic orbits, and proper closed "
                    + "subgroups are included. In one coordinate g = -1 retains the even "
                    + "integer relation lattice and the two-point subgroup. The statement "
                    + "asserts a topological characterization, with no algorithm for finding "
                    + "a finite generating family of integer relations."))),
            DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Arrow(Formula left, Formula right) =>
        new Formula.TypeArrow(left, right);

    private static Formula Character(string point) =>
        Seq(Prod, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("I")), Sp,
            new Formula.Power(Call(point, F.Id("i")), Call("k", F.Id("i"))));

    private static Formula OrbitFormula()
    {
        Formula circle = F.Id("Circle");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula orbit = new Formula.SetBuilder(
            new Formula.Power(F.Id("g"), F.Id("n")), F.Id("n"), naturals);
        Formula membership = new Formula.Relation(F.Id("z"), FormulaRelationOperator.MemberOf,
            Call("closure", orbit));
        Formula relations = All("k", Arrow(F.Id("I"), integers),
            new Formula.Logic(Equal(Character("g"), D(1)), FormulaLogicOperator.Implies,
                Equal(Character("z"), D(1))));
        return Disp(All("I", F.Id("FiniteType"),
            All("g", Arrow(F.Id("I"), circle), All("z", Arrow(F.Id("I"), circle),
                new Formula.Logic(membership, FormulaLogicOperator.Iff, relations)))));
    }
}
