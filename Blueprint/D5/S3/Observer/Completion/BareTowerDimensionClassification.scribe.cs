using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class BareTowerDimensionClassificationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/BareTowerDimensionClassification."
            + "bare_tower_dimension_classification";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bare orthogonal Hilbert tower is classified by the Hilbert dimensions of its "
            + "initial block, every shell, and its terminal residual.",
        H("Bare Tower Dimension Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bare-tower-dimension-classification"),
                DeclarationHandle.Create(Declaration),
                H("Block dimensions classify bare towers"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The block index has one initial coordinate, one coordinate for every "
                            + "natural-numbered shell, and one terminal residual coordinate. "
                            + "The ambient carrier is their canonical square-summable Hilbert "
                            + "sum.")),
                    Paragraph(Text(
                        "Tower equivalence is witnessed by a global unitary together with its "
                            + "unitary computation rule on every canonical block embedding.")),
                    Paragraph(Text(
                        "Two blocks have the same Hilbert dimension when each admits a Hilbert "
                            + "basis on one common index type. Basis representations construct "
                            + "the block unitaries, and the local square-summable bridge assembles "
                            + "them into the global unitary."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula SameDimension(
        Formula scalar,
        Formula left,
        Formula right)
    {
        Formula index = F.Id("J");
        Formula leftBasis = Call("HilbertBasis", index, scalar, left);
        Formula rightBasis = Call("HilbertBasis", index, scalar, right);
        return new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("J", F.Id("Type"))],
            And(Call("Nonempty", leftBasis), Call("Nonempty", rightBasis)));
    }

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula naturals = F.Id("Nat");
        Formula scalar = F.Id("K");
        Formula block = F.Id("B");
        Formula blockPrime = F.Id("Bprime");
        Formula indexType = Call("Option", Call("Option", naturals));
        Formula blockFamilyType = Arrow(indexType, type);
        Formula index = F.Id("i");
        Formula shellNumber = F.Id("n");
        Formula vector = F.Id("x");
        Formula globalUnitary = F.Id("U");
        Formula blockUnitary = F.Id("u");

        Formula BlockAt(Formula family, Formula at) => Apply(family, at);
        Formula HilbertSum(Formula family) => Call("lp", family, F.D(2));
        Formula Unitary(Formula left, Formula right) =>
            Call("LinearIsometryEquiv", scalar, left, right);
        Formula blockAtIndex = BlockAt(block, index);
        Formula blockPrimeAtIndex = BlockAt(blockPrime, index);

        Formula familyInstances(Formula family) => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            And(
                Call("NormedAddCommGroup", BlockAt(family, index)),
                And(
                    Call("InnerProductSpace", scalar, BlockAt(family, index)),
                    Call("CompleteSpace", BlockAt(family, index)))));

        Formula instances = And(
            Call("RCLike", scalar),
            And(familyInstances(block), familyInstances(blockPrime)));

        Formula blockUnitaryType = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Unitary(blockAtIndex, blockPrimeAtIndex));
        Formula sourceSingle = Call("single", F.D(2), index, vector);
        Formula targetSingle = Call(
            "single",
            F.D(2),
            index,
            Apply(Apply(blockUnitary, index), vector));
        Formula blockComputation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("x", blockAtIndex)],
            new Formula.Relation(
                Apply(globalUnitary, sourceSingle),
                FormulaRelationOperator.Equal,
                targetSingle));
        Formula towerEquivalence = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound(
                "U",
                Unitary(HilbertSum(block), HilbertSum(blockPrime)))],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("u", blockUnitaryType)],
                blockComputation));

        Formula initial = Call("none");
        Formula shell = Call("some", Call("some", shellNumber));
        Formula residual = Call("some", Call("none"));
        Formula initialDimension = SameDimension(
            scalar, BlockAt(block, initial), BlockAt(blockPrime, initial));
        Formula shellDimensions = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            SameDimension(
                scalar, BlockAt(block, shell), BlockAt(blockPrime, shell)));
        Formula residualDimension = SameDimension(
            scalar, BlockAt(block, residual), BlockAt(blockPrime, residual));
        Formula dimensions = And(
            initialDimension,
            And(shellDimensions, residualDimension));
        Formula classification = new Formula.Logic(
            towerEquivalence,
            FormulaLogicOperator.Iff,
            dimensions);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("K", type),
                Bound("B", blockFamilyType),
                Bound("Bprime", blockFamilyType),
            ],
            new Formula.Logic(
                instances,
                FormulaLogicOperator.Implies,
                classification)));
    }
}
