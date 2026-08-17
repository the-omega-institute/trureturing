using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class DBonacciGeneralTribonacciFiniteNameBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var x = Id("x");
        var t = Id("t");
        var carrier = Id("Dfin");
        var naturals = Id("N");
        var reals = Id("R");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        Formula Liminf(Formula point) =>
            Call("liminfAtTop", Call("tribonacciSurvivor", q, point));

        var carrierDefinition = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Logic(
                Member(x, carrier),
                FormulaLogicOperator.Iff,
                new Formula.Bind(
                    FormulaQuantifier.Exists,
                    FormulaIdentifier.Create("Q"),
                    naturals,
                    Member(x, Call("tribonacciNameGrid", q)))));
        var zeroLiminf = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            carrier,
            Equal(Liminf(x), Num(0)));
        var boundedLiminf = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            carrier,
            new Formula.Relation(
                Liminf(x),
                FormulaRelationOperator.LessThanOrEqual,
                Call("championValue", t)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Terminating Tribonacci names have zero survivor liminf and satisfy the corrected "
                + "champion upper bound.",
            H("Tribonacci Finite-Name Bound"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("terminating-tribonacci-name-carrier"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound."
                        + "tribonacciFiniteNameCarrier"),
                    H("Terminating-name carrier"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(carrierDefinition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The carrier is the union of all finite Tribonacci name grids. This is an "
                            + "arithmetic domain selected by terminating admissible expansions, "
                            + "not a predicate manufactured only to remove the endpoint "
                            + "counterexample."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("finite-tribonacci-names-have-zero-liminf"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound."
                        + "tribonacci_finite_name_liminf"),
                    H("Finite names have zero liminf"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(zeroLiminf)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Appending zero digits preserves an admissible name and its real value. "
                            + "Consequently a point in one finite grid belongs to every later "
                            + "grid, "
                            + "so its normalized grid distance is eventually identically zero."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("finite-tribonacci-name-champion-upper-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound."
                        + "tribonacci_finite_name_liminf_upper_bound"),
                    H("Champion bound on finite names"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(boundedLiminf)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact zero liminf lies below the positive Tribonacci champion value. "
                            + "This theorem covers only terminating name points. It does not prove "
                            + "the source sentence on the full interior interval, and it does not "
                            + "include the nonterminating champion orbit."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound")),
            ]));
    }
}
