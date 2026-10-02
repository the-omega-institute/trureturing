using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealIntervalUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual arrow-image ranks determine all finite interval endpoint multiplicities.",
        H("Real Interval Sums and Arbitrary Endpoint Uniqueness"),
        Blocks(
            Definition("interval-family", "IntervalFamily", "Positive finite or essential intervals",
                "An occurrence has a real birth and a death in WithTop(Real), strictly greater than "
                    + "birth. Infinity is allowed. Repeated intervals retain separate occurrences."),
            Definition("interval-space", "intervalSpace", "The actual supported coordinate subspace",
                "At time r this is the subspace of K-valued occurrence coordinates that vanish "
                    + "unless birth <= r < death. The field is arbitrary."),
            Definition("interval-arrow", "intervalArrow", "The actual structure map",
                "For s <= t, retain source coordinates whose deaths are strictly above t and kill "
                    + "the others. The output lies in the supported subspace at t."),
            Definition("interval-sum", "intervalSum", "A real persistence functor",
                "The supported spaces and actual arrows form a functor from the real preorder to "
                    + "ModuleCat. The definition checks identity and composition, including exact "
                    + "birth/death points, zero spaces and infinite tails."),
            Describe.Lean(
                DescribeId.Create("ranks-determine-multiplicities"),
                DeclarationHandle.Create(Prefix + "ranks_determine_multiplicities"),
                H("Recovering multiplicities across arbitrary endpoint sets"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "K is any field. The two occurrence types are finite and their intervals "
                            + "have positive length. Equality of the dimensions of the actual "
                            + "arrow images for every real s <= t implies equality of occurrence "
                            + "counts at every real birth and every finite or infinite death.")),
                    Paragraph(Text(
                        "The proof identifies each actual image with the functions on precisely "
                            + "the surviving occurrences, constructing a source lift and the "
                            + "inverse restriction. A common finite set of endpoints supplies "
                            + "source cuts isolating a birth, target cuts isolating a finite death, "
                            + "and a final cut past all finite deaths for essential intervals. "
                            + "Integer differences are taken only after these cuts are proved valid.")),
                    Paragraph(Text(
                        "No common input grid, assumed barcode classifier or prescribed target "
                            + "identity is supplied. Empty occurrence types and repeated intervals "
                            + "are included. This theorem does not construct induced matchings, "
                            + "quantitative stability or an interleaving isometry."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string id, string declaration, string heading, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ResultFormula()
    {
        Formula field = F.Id("K"), first = F.Id("A"), second = F.Id("B");
        Formula sameRanks = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("s", Call("Real")), Bound("t", Call("Real"))],
            new Formula.Logic(new Formula.Relation(F.Id("s"), FormulaRelationOperator.LessThanOrEqual, F.Id("t")),
                FormulaLogicOperator.Implies,
                new Formula.Relation(Call("finrank", field, Call("range", Call("intervalArrow", first, F.Id("s"), F.Id("t")))),
                    FormulaRelationOperator.Equal,
                    Call("finrank", field, Call("range", Call("intervalArrow", second, F.Id("s"), F.Id("t")))))));
        Formula counts = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("birth", Call("Real")), Bound("death", Call("WithTop", Call("Real")))],
            new Formula.Relation(Call("endpointMultiplicity", first, F.Id("birth"), F.Id("death")),
                FormulaRelationOperator.Equal,
                Call("endpointMultiplicity", second, F.Id("birth"), F.Id("death"))));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("K", F.Id("Type")), Bound("A", Call("FinitePositiveIntervalFamily")),
                Bound("B", Call("FinitePositiveIntervalFamily"))],
            new Formula.Logic(Call("Field", field), FormulaLogicOperator.Implies,
                new Formula.Logic(sameRanks, FormulaLogicOperator.Implies, counts))));
    }
}
