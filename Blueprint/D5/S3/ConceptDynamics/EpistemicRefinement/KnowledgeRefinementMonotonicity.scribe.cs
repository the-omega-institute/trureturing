using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EpistemicRefinement;

internal sealed class KnowledgeRefinementMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EpistemicRefinement/KnowledgeRefinementMonotonicity."
            + "knowledge_monotone_under_indexed_refinement_with_converse_countermodel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Knowledge by factorization is monotone under indexed readout refinement.",
        H("Knowledge Refinement Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("knowledge-monotone-under-indexed-refinement-with-converse-countermodel"),
            DeclarationHandle.Create(Declaration),
            H("Refinement preserves knowledge but coarsening need not"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Knowledge is displayed directly as factorization of the target through the "
                        + "canonical joint readout. For nested finite budgets, restriction from the "
                        + "fine joint output to the coarse output supplies the readout refinement.")),
                Paragraph(Text(
                    "Composing the coarse target factor with that restriction proves the first "
                        + "public clause for arbitrary state, output, and target carriers. No "
                        + "separate knowledge predicate or joint-readout construction is declared.")),
                Paragraph(Text(
                    "The second public clause is a shared countermodel: one Boolean target, one "
                        + "indexed Boolean readout, and nested budgets jointly witness fine "
                        + "knowledge and the absence of coarse knowledge. Its positive and negative "
                        + "parts therefore cannot be separated into unrelated constructions."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula targetType = F.Id("T");
        Formula readout = F.Id("q");
        Formula target = F.Id("P");
        Formula coarse = F.Id("J");
        Formula fine = F.Id("K");
        Formula type = F.Id("Type");

        Formula BudgetReadout(Formula q, Formula budget) =>
            Call("jointReadout", Call("restrict", q, budget));
        Formula Knows(Formula q, Formula budget, Formula predicate) =>
            Call("Refines", predicate, BudgetReadout(q, budget));

        Formula monotonicity = Seq(
            Forall, Sp, index, Comma, Sp, state, Comma, Sp, targetType,
            Colon, Sp, type, Comma, Sp,
            output, Colon, Sp, index, Sp, To, Sp, type, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Forall, Sp, F.Id("i"), Colon, Sp, index,
            Comma, Sp, state, Sp, To, Sp, Apply(output, F.Id("i")), Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetType, Comma,
            RowBreak, Grp(),
            coarse, Comma, Sp, fine, InMacro, Sp, Call("Finset", index), Comma, Sp,
            coarse, Sp, Subseteq, Sp, fine, Sp, Rightarrow, Sp,
            Open, Knows(readout, coarse, target), Sp, Rightarrow, Sp,
            Knows(readout, fine, target), Close);

        Formula countermodel = Seq(
            Exists, Sp, readout, Colon, Sp,
            F.Id("Unit"), Sp, To, Sp, Open, F.Id("Bool"), Sp, To, Sp,
            F.Id("Bool"), Close, Comma, Sp,
            target, Colon, Sp, F.Id("Bool"), Sp, To, Sp, F.Id("Bool"), Comma,
            RowBreak, Grp(),
            coarse, Comma, Sp, fine, InMacro, Sp, Call("Finset", F.Id("Unit")),
            Comma, Sp, coarse, Sp, Subseteq, Sp, fine,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Knows(readout, fine, target),
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Neg, Sp, Knows(readout, coarse, target));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, monotonicity, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, countermodel, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
