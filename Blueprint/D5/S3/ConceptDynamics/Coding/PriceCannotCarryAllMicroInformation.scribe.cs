using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class PriceCannotCarryAllMicroInformationDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Coding/PriceCannotCarryAllMicroInformation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A price strictly coarser than a joint micro-readout misses a target, while a "
            + "faithful price carries every target determined by that readout.",
        H("Price Cannot Carry All Micro-Information"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strictly-coarser-price-misses-a-joint-target"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "strictly_coarser_price_misses_some_target"),
                H("A strictly coarser price misses a joint target"),
                StatementSource.FromAuthor(StrictlyCoarserPriceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joint readout itself supplies the missing target. It is determined "
                            + "by the joint information through the identity factor map.")),
                    Paragraph(Text(
                        "Strict coarseness says that this joint readout cannot factor through "
                            + "the price. The target is therefore explicit: no cardinality or "
                            + "choice argument is needed to find information that the price "
                            + "fails to carry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faithful-price-carries-every-join-target"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "faithful_price_carries_every_join_target"),
                H("A faithful price carries every joint target"),
                StatementSource.FromAuthor(FaithfulPriceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the joint readout factors through the price, every target already "
                        + "determined by that readout also factors through the price. Composing "
                        + "the two factor maps proves that a faithful price loses none of the "
                        + "targets supported by the joint micro-information."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("first-coordinate-price-is-strictly-coarser"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "coordinate_price_strictly_coarser"),
                H("The first-coordinate price is strictly coarser"),
                StatementSource.FromAuthor(CoordinatePriceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a pair of Boolean coordinates, the coordinate price retains only "
                            + "the first coordinate. Projection from the joint readout recovers "
                            + "that price, so the joint readout refines it.")),
                    Paragraph(Text(
                        "The states (false, false) and (false, true) have the same price but "
                            + "different second coordinates. Hence the full joint readout cannot "
                            + "factor back through the price, making the refinement genuinely "
                            + "strict."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula Refines(Formula target, Formula information) =>
        Call("Refines", target, information);

    private static Formula StrictRefinement(Formula coarse, Formula fine) =>
        Call("StrictRefinement", coarse, fine);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula StrictlyCoarserPriceFormula()
    {
        Formula state = F.Id("X");
        Formula priceType = F.Id("Price");
        Formula firstType = F.Id("C1");
        Formula secondType = F.Id("C2");
        Formula price = F.Id("price");
        Formula firstConcept = F.Id("q1");
        Formula secondConcept = F.Id("q2");
        Formula target = F.Id("target");
        Formula join = Join(firstConcept, secondConcept);
        Formula targetClaim = new Formula.Logic(
            Refines(target, join),
            FormulaLogicOperator.And,
            new Formula.Not(Refines(target, price)));
        Formula missedTarget = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("target"),
            Arrow(state, Product(firstType, secondType)),
            targetClaim);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("Price", F.Id("Type")),
                Bound("C1", F.Id("Type")),
                Bound("C2", F.Id("Type")),
                Bound("price", Arrow(state, priceType)),
                Bound("q1", Arrow(state, firstType)),
                Bound("q2", Arrow(state, secondType)),
            ],
            new Formula.Logic(
                StrictRefinement(price, join),
                FormulaLogicOperator.Implies,
                missedTarget)));
    }

    private static Formula FaithfulPriceFormula()
    {
        Formula state = F.Id("X");
        Formula priceType = F.Id("Price");
        Formula firstType = F.Id("C1");
        Formula secondType = F.Id("C2");
        Formula targetType = F.Id("Target");
        Formula price = F.Id("price");
        Formula firstConcept = F.Id("q1");
        Formula secondConcept = F.Id("q2");
        Formula target = F.Id("target");
        Formula join = Join(firstConcept, secondConcept);
        Formula premises = new Formula.Logic(
            Refines(join, price),
            FormulaLogicOperator.And,
            Refines(target, join));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("Price", F.Id("Type")),
                Bound("C1", F.Id("Type")),
                Bound("C2", F.Id("Type")),
                Bound("Target", F.Id("Type")),
                Bound("price", Arrow(state, priceType)),
                Bound("q1", Arrow(state, firstType)),
                Bound("q2", Arrow(state, secondType)),
                Bound("target", Arrow(state, targetType)),
            ],
            new Formula.Logic(
                premises,
                FormulaLogicOperator.Implies,
                Refines(target, price))));
    }

    private static Formula CoordinatePriceFormula()
    {
        Formula coordinatePrice = F.Id("coordinatePrice");
        Formula secondCoordinate = F.Id("snd");

        return Disp(StrictRefinement(
            coordinatePrice,
            Join(coordinatePrice, secondCoordinate)));
    }
}
