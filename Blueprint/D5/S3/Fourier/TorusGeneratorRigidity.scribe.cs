using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class TorusGeneratorRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous family of torus points with the same actual power-orbit closure is constant on every preconnected parameter subset.",
        H("Rigidity of Torus Generators"),
        Blocks(Describe.Lean(
            DescribeId.Create("torus-generator-rigidity"),
            DeclarationHandle.Create("D5/S3/Fourier/TorusGeneratorRigidity.result"),
            H("A common orbit closure forces constancy"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let P be any topological space, I any index type, S a preconnected "
                    + "subset of P, and g a function from P to the product of circles indexed "
                    + "by I. Assume that g is continuous on S. If the closure of the actual "
                    + "set of nonnegative integer powers of g(p) is one fixed set G for every "
                    + "p in S, then g(p) equals g(q) for every p and q in S.")),
                Paragraph(Text(
                    "No finiteness or nonemptiness of I is required. The statement includes "
                    + "empty S, empty parameter spaces, and the empty product. G need not be "
                    + "specified as a subgroup or assumed connected. In particular, finite, "
                    + "proper, and disconnected compact orbit subgroups are all included.")),
                Paragraph(Text(
                    "For each circle coordinate, if one value has finite order, its finite "
                    + "set of powers is closed. The common orbit closure places every other "
                    + "coordinate value in this same finite set, so preconnectedness forces "
                    + "constancy. Otherwise all coordinate values have infinite order. "
                    + "The circle is identified with the additive circle of period one, "
                    + "and its representative in the interval [0,1) is continuous because "
                    + "the family avoids the identity. Every representative is irrational. "
                    + "Two distinct values would force a rational intermediate value, "
                    + "a contradiction. Coordinate equality gives equality in the product.")),
                Paragraph(Text(
                    "Taking S to be the whole connected parameter space gives constancy "
                    + "of the family. Taking S to be any connected component gives componentwise "
                    + "constancy on an arbitrary parameter space. The finite-power, quotient-circle, "
                    + "and intermediate-value steps use the corresponding Mathlib results. "
                    + "The common-closure hypothesis is essential: the family exp(it) "
                    + "on the real line is continuous and nonconstant."))),
            DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);

    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);

    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);

    private static Formula Statement()
    {
        Formula pType = F.Id("P");
        Formula index = F.Id("I");
        Formula subset = F.Id("S");
        Formula g = F.Id("g");
        Formula group = F.Id("G");
        Formula torus = new Formula.Power(Call("Circle"), index);
        Formula gp = Call("g", F.Id("p"));
        Formula powers = Call("range", Seq(F.Id("n"), Mapsto,
            new Formula.Power(gp, F.Id("n"))), Call("NaturalNumbers"));
        Formula common = All("p", subset, Eq(Call("closure", powers), group));
        Formula hypotheses = And(Call("IsPreconnected", subset),
            And(Call("ContinuousOn", g, subset), common));
        Formula conclusion = All("p", subset, All("q", subset,
            Eq(gp, Call("g", F.Id("q")))));
        return Disp(All("P", Call("TopologicalSpaces"), All("I", Call("Types"),
            All("S", Call("Subsets", pType),
                All("g", Seq(pType, Rightarrow, torus),
                    All("G", Call("Subsets", torus),
                        Seq(hypotheses, Rightarrow, conclusion)))))));
    }
}
