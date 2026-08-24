using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Algebra;

internal sealed class FinitePartitionAlgebraDualityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivalence relations and finite unital pointwise algebras of real functions determine "
            + "each other, and both finiteness and each closure condition are necessary.",
        H("Finite Partition Algebra Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("indistinguishability-recovers-every-relation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "indistinguishability_partitionAlgebra"),
                H("Partition functions recover every relation"),
                StatementSource.FromAuthor(RelationRoundTripFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Functions constant on the classes of a relation cannot separate related "
                            + "states, and the indicator of one class separates any unrelated "
                            + "pair. The relation is therefore reconstructed exactly.")),
                    Paragraph(Text(
                        "This direction needs no finiteness hypothesis on the state type and no "
                            + "closure hypothesis on the algebra."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-algebra-recovers-itself"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "partitionAlgebra_indistinguishability"),
                H("Finite unital algebras recover exactly their own blocks"),
                StatementSource.FromAuthor(AlgebraRoundTripFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every member of the algebra is constant on its indistinguishability "
                            + "classes, giving one inclusion with no extra hypothesis.")),
                    Paragraph(Text(
                        "For the reverse inclusion, a finite state type has finitely many "
                            + "classes. Each class indicator lies in the algebra, and a function "
                            + "constant on classes is the finite linear combination of those "
                            + "indicators weighted by its class values, hence lies in the "
                            + "algebra."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiteness-is-necessary"),
                DeclarationHandle.Create(DeclarationPrefix + "finiteness_is_necessary"),
                H("Dropping finiteness breaks the algebra round trip"),
                StatementSource.FromAuthor(FinitenessNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the natural numbers the eventually constant real sequences form a "
                            + "unital algebra closed under linear combinations and products, and "
                            + "they separate every pair of indices.")),
                    Paragraph(Text(
                        "Its indistinguishability relation is therefore equality, whose partition "
                            + "algebra is all real sequences. The identity sequence is constant "
                            + "on singleton classes yet is not eventually constant, so the round "
                            + "trip strictly enlarges the algebra."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("constants-are-necessary"),
                DeclarationHandle.Create(DeclarationPrefix + "constants_are_necessary"),
                H("Dropping the constants breaks the algebra round trip"),
                StatementSource.FromAuthor(ConstantsNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The family containing only the zero function on a two-element state type "
                            + "is closed under linear combinations and under pointwise products, "
                            + "but contains no nonzero constant.")),
                    Paragraph(Text(
                        "It separates nothing, so its indistinguishability relation is total and "
                            + "its partition algebra is every constant function. That algebra "
                            + "strictly contains the original family."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("linear-combinations-are-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "linear_combinations_are_necessary"),
                H("Dropping linear combinations breaks the algebra round trip"),
                StatementSource.FromAuthor(LinearCombinationsNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a two-element state type the constants together with the scalar "
                            + "multiples of one block indicator are closed under pointwise "
                            + "products and already separate the two states.")),
                    Paragraph(Text(
                        "That family omits the sums of its own members, so its partition algebra "
                            + "is strictly larger. Closure under linear combinations is therefore "
                            + "not removable."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("pointwise-multiplication-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "pointwise_multiplication_is_necessary"),
                H("Dropping pointwise products breaks the algebra round trip"),
                StatementSource.FromAuthor(PointwiseMultiplicationNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The affine functions of the coordinate on a three-element state type "
                            + "contain the constants, are closed under linear combinations, and "
                            + "separate all three states.")),
                    Paragraph(Text(
                        "The square of the coordinate is constant on the resulting singleton "
                            + "classes yet is not affine, so the partition algebra strictly "
                            + "contains the family. Closure under products is therefore not "
                            + "removable."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() => Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula RealNumbers() => F.Id("R");

    private static Formula Named(string name) =>
        Seq(Operatorname, Grp(F.Id(name)));

    private static Formula RelationRoundTripFormula()
    {
        Formula stateType = F.Id("X");
        Formula relation = F.Id("R");
        Formula roundTrip = Apply(
            Named("Indistinguishable"),
            Apply(Named("partitionAlgebra"), relation));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Colon, Sp, TypeUniverse(), Comma, Sp,
            Typed(relation, Apply(Named("Setoid"), stateType)), Comma, RowBreak, Grp(),
            roundTrip, Sp, Eq, Sp, relation, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula AlgebraRoundTripFormula()
    {
        Formula stateType = F.Id("X");
        Formula algebra = F.Id("A");
        Formula roundTrip = Apply(
            Named("partitionAlgebra"),
            Apply(Named("indistinguishabilitySetoid"), algebra));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Colon, Sp, TypeUniverse(), Comma, Sp,
            Named("Fintype"), Sp, stateType, Comma, RowBreak, Grp(),
            Typed(
                algebra,
                Apply(Named("Subalgebra"), RealNumbers(), Arrow(stateType, RealNumbers()))),
            Comma, RowBreak, Grp(),
            roundTrip, Sp, Eq, Sp, algebra, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FinitenessNecessaryFormula()
    {
        Formula algebra = Named("eventuallyConstantAlgebra");
        Formula roundTrip = Apply(
            Named("partitionAlgebra"),
            Apply(Named("indistinguishabilitySetoid"), algebra));

        return Disp(Seq(roundTrip, Sp, Neq, Sp, algebra, Dot));
    }

    private static Formula ExistsWitnessFormula(
        Formula stateType,
        Formula firstClosure,
        Formula secondClosure)
    {
        Formula algebra = F.Id("A");
        Formula roundTrip = Apply(
            Named("RelationInvariantFunctions"),
            Apply(Named("Indistinguishable"), algebra));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            Typed(algebra, Apply(Named("Set"), Arrow(stateType, RealNumbers()))),
            Comma, RowBreak, Grp(),
            Apply(firstClosure, algebra), Sp, Land, Sp,
            Apply(secondClosure, algebra), Sp, Land, RowBreak, Grp(),
            roundTrip, Sp, Neq, Sp, algebra, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula LinearCombinationsNecessaryFormula() =>
        ExistsWitnessFormula(
            F.Id("Bool"),
            Named("ContainsConstants"),
            Named("ClosedUnderPointwiseMultiplication"));

    private static Formula PointwiseMultiplicationNecessaryFormula() =>
        ExistsWitnessFormula(
            Apply(Named("Fin"), F.Id("3")),
            Named("ContainsConstants"),
            Named("ClosedUnderLinearCombinations"));

    private static Formula ConstantsNecessaryFormula()
    {
        Formula algebra = F.Id("A");
        Formula boolType = F.Id("Bool");
        Formula roundTrip = Apply(
            Named("RelationInvariantFunctions"),
            Apply(Named("Indistinguishable"), algebra));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            Typed(algebra, Apply(Named("Set"), Arrow(boolType, RealNumbers()))),
            Comma, RowBreak, Grp(),
            Apply(Named("ClosedUnderLinearCombinations"), algebra), Sp, Land, Sp,
            Apply(Named("ClosedUnderPointwiseMultiplication"), algebra), Sp, Land, RowBreak,
            Grp(),
            roundTrip, Sp, Neq, Sp, algebra, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
