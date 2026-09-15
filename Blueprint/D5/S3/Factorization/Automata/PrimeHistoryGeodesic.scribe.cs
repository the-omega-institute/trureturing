using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeHistoryGeodesicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact contextual behavior has a shortest three-run representative, with a matching all-word bound.",
        H("Shortest Prime History Representatives"),
        Blocks(
            Paragraph(Text(
                "For a nonempty interval translation [l,u] with final displacement d in "
                + "capacity a, the necessary visited displacement interval is [-l,a-u]. "
                + "Every realizing history must account for both extrema. A word with the "
                + "same net displacement but a smaller excursion would have a different "
                + "legal starting-state set, and is not an admissible replacement.")),
            Describe.Lean(
                DescribeId.Create("prime-history-sharp-representative"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryGeodesic.shortest_realization"),
                H("The lower bound is attained by an explicit word"),
                StatementSource.FromAuthor(ShortestRealizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative d, use the earlier lower-first realization. For negative "
                    + "d, reflect the capacity interval, realize the reflected form, then "
                    + "exchange multiplication and division. The proof computes its exact "
                    + "signature and length. Uniqueness of a nonempty normal form forces every "
                    + "competing word to have the same extrema and final displacement, so the "
                    + "all-word lower bound proves optimality. This is minimum operation count "
                    + "inside a contextual behavior class, not recovery of the original "
                    + "history's length and not a preservation theorem for other costs."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/PrimeHistoryNormalForm")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/WordExcursionLowerBound"))
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() => new Formula.Integers();

    private static Formula Words() => Call("List", F.Id("Bool"));

    private static Formula IntervalMaps() => Call("IntervalMap", F.Id("a"));

    private static Formula Field(string name) => Seq(F.Id("t"), Dot, F.Id(name));

    private static Formula ShortestWord() => Call("shortestWord", F.Id("t"));

    private static Formula Length(Formula word) => QualifiedCall("List", "length", word);

    private static Formula Normal(Formula word) => Call("normal", F.Id("a"), word);

    private static Formula IntCast(Formula value) =>
        Seq(Open, value, Colon, Sp, Integers(), Close);

    private static Formula ExactLength() => new Formula.Binary(
        new Formula.Binary(
            D(2),
            FormulaBinaryOperator.Multiply,
            new Formula.Binary(
                new Formula.Binary(
                    IntCast(F.Id("a")),
                    FormulaBinaryOperator.Subtract,
                    Field("hi")),
                FormulaBinaryOperator.Add,
                Field("lo"))),
        FormulaBinaryOperator.Subtract,
        Call("max", Field("shift"), new Formula.Negate(Field("shift"))));

    private static Formula ShortestRealizationFormula() => Disp(Universal("a", Naturals(),
        Universal("t", IntervalMaps(),
            And(
                Equal(Normal(ShortestWord()), Call("some", F.Id("t"))),
                And(
                    Equal(IntCast(Length(ShortestWord())), ExactLength()),
                    Universal("w", Words(),
                        Implies(
                            Equal(Normal(F.Id("w")), Call("some", F.Id("t"))),
                            LessOrEqual(Length(ShortestWord()), Length(F.Id("w"))))))))));
}
