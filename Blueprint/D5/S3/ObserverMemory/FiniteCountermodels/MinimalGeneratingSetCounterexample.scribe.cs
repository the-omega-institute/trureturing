using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class MinimalGeneratingSetCounterexampleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Boolean square has deletion-minimal concept generators of cardinalities one and two.",
        H("Minimal Generators Need Not Have One Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-square-has-minimal-generators-of-sizes-one-and-two"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FiniteCountermodels/"
                        + "MinimalGeneratingSetCounterexample."
                        + "boolean_square_has_minimal_generators_of_sizes_one_and_two"),
                H("The Boolean square has differently sized minimal generators"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state carrier is the Boolean square. The identity concept returns the "
                            + "whole state, while the two coordinate concepts return the first and "
                            + "second bits. Their common sum codomain only makes the finite family "
                            + "homogeneous; equality of each readout has exactly the source meaning.")),
                    Paragraph(Text(
                        "A family generates top_X when agreement on every member forces equality of "
                            + "states. A finite family is minimal when deleting any one member destroys "
                            + "that separation property. Thus the definition records genuine proper-"
                            + "subgenerator minimality rather than merely irredundancy by cardinality.")),
                    Paragraph(Text(
                        "The identity singleton separates all states and its deletion does not. The two "
                            + "coordinates jointly separate states, while deleting either leaves one pair "
                            + "of states indistinguishable. The resulting finite certificates have cards "
                            + "one and two. Repository and pinned-library searches found no equal theorem."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Seq(function, Open, Seq(arguments), Close);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Set(params Formula[] values) => new Formula.SetLiteral([.. values]);

    private static Formula Gen(Formula family) => Apply(F.Id("Gen"), family);

    private static Formula Minimal(Formula family) => Apply(F.Id("Minimal"), family);

    private static Formula Card(Formula family) => Apply(F.Id("card"), family);

    private static Formula TheoremFormula()
    {
        Formula c = F.Id("C");
        Formula cOne = Sub(c, D(1));
        Formula cTwo = Sub(c, D(2));
        Formula cThree = Sub(c, D(3));
        Formula xOne = Sub(F.Id("x"), D(1));
        Formula xTwo = Sub(F.Id("x"), D(2));
        Formula state = Seq(Open, xOne, Comma, Sp, xTwo, Close);
        Formula singleton = Set(cOne);
        Formula coordinates = Set(cTwo, cThree);
        Formula all = Set(cOne, cTwo, cThree);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            F.Id("X"), Eq, Set(D(0), D(1)), Caret, D(2), Comma, RowBreak,
            Apply(cOne, state), Eq, state, Comma, Sp,
            Apply(cTwo, state), Eq, xOne, Comma, Sp,
            Apply(cThree, state), Eq, xTwo, Comma, RowBreak,
            Gen(all), Sp, Land, Sp, Minimal(singleton), Sp, Land, Sp,
            Minimal(coordinates), Comma, RowBreak,
            Card(singleton), Eq, D(1), Sp, Land, Sp,
            Card(coordinates), Eq, D(2), Sp, Land, Sp,
            D(1), Sp, Neq, Sp, D(2), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
