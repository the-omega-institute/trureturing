using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CommonSpectralPerturbationsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CommonSpectralPerturbations";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One frequency assignment can satisfy a family of weighted collision bounds.",
        H("Common Spectral Perturbations for Finite-Resolution Tests"),
        Blocks(
            Paragraph(Text(
                "Let J have decidable equality and let K index the tests. Each j in J has a frequency "
                + "g(j), a positive radius ε(j) and M(j)+2 allowed offsets, indexed by Fin(M(j)+2). "
                + "An index f(j) defines H(f,j) = g(j) + ε(j)(2f(j)/(M(j)+1) − 1). "
                + "Each k in K uses a finite support J(k), nonnegative weights on that support, "
                + "a natural degree p(k) and a nonnegative resolution η(k).")),
            Paragraph(Text(
                "For test k, let E(k,h) be its weighted near-collision mass for the restriction of "
                + "h to J(k). Write D(k) for the diagonal mass and B(k) for the full off-diagonal "
                + "weight W(k) raised to 2p(k), minus D(k). Choose b(k)>0. Take ρ(k) to be any "
                + "upper bound on the fraction min(M(j)+2, 1+floor(η(k)(M(j)+1)/ε(j)))/(M(j)+2) "
                + "for every j in J(k). The budget term A(k) equals ρ(k)/b(k) when B(k)>0, "
                + "and is zero when B(k)=0.")),
            Describe.Lean(
                DescribeId.Create("exists-common-nearby-collision-bounds"),
                DeclarationHandle.Create(Owner + ".exists_common_nearby_collision_bounds"),
                H("One grid choice for all tests"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a finite subfamily and average over the grids of the union of their "
                        + "supports. Each restricted assignment occurs the same number of times. "
                        + "The affine fiber count on the support bounds the mean of the excess "
                        + "E(k,h)−D(k) by ρ(k)B(k). Every such excess is nonnegative and at most B(k), "
                        + "so tests with B(k)=0 hold for every assignment.")),
                    Paragraph(Text(
                        "Divide each positive-mass excess by b(k)B(k). If every assignment violates "
                        + "a test, the sum of these normalized excesses exceeds one at every point "
                        + "of the finite product. Its mean is at most the total budget, which also "
                        + "gives the result at budget one. Each test defines a closed cylinder set "
                        + "in the compact product of finite discrete grids. The finite-intersection "
                        + "property gives one assignment for the whole family.")),
                    Paragraph(Text(
                        "The positive radius gives nonzero grid spacing. The positive tolerance "
                        + "permits the normalization used in the bound at budget one. The nonnegative "
                        + "weights give nonnegative ordered-pair masses. A zero resolution includes "
                        + "the diagonal, and a negative resolution gives zero collision mass. "
                        + "The simultaneous conclusion concerns perturbations of comparison spectra. "
                        + "Preserving a prescribed counting law requires a separate estimate for the "
                        + "chosen radii. For the fixed actual zeta ordinates the collision estimates "
                        + "still require arithmetic input."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Bound()
    {
        var k = F.Id("k");
        var j = F.Id("j");
        var h = F.Id("h");
        var f = F.Id("f");
        var tests = F.Id("T");
        var indices = F.Id("J");
        var testIndices = F.Id("K");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var grid = Seq(Operatorname, Grp(F.Id("Fin")), Open, Add(Call("M", j), D(2)), Close);
        var assignmentType = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, indices)), grid);
        var finiteSubsets = Seq(Operatorname, Grp(F.Id("Finset")), Open, testIndices, Close);
        var totalBudget = Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, tests)), Call("A", k));
        var budget = Bind(FormulaQuantifier.ForAll, "T", finiteSubsets, AtMost(totalBudget, D(1)));
        var distance = new Formula.Absolute(Seq(Call("h", j), Minus, Call("g", j)));
        var radius = Seq(Varepsilon, Open, j, Close);
        var proximity = Bind(FormulaQuantifier.ForAll, "j", indices, AtMost(distance, radius));
        var gridPoint = new Formula.Relation(Call("h", j), FormulaRelationOperator.Equal, Call("H", f, j));
        var gridWitness = Bind(FormulaQuantifier.Exists, "f", assignmentType,
            Bind(FormulaQuantifier.ForAll, "j", indices, gridPoint));
        var collision = Bind(FormulaQuantifier.ForAll, "k", testIndices,
            AtMost(Call("E", k, h), Add(Call("D", k), Multiply(Call("b", k), Call("B", k)))));
        var law = Bind(FormulaQuantifier.Exists, "h", Seq(indices, Sp, To, Sp, reals),
            And(proximity, And(Seq(Open, gridWitness, Close), collision)));
        return Disp(new Formula.Logic(budget, FormulaLogicOperator.Implies, law));
    }
}
