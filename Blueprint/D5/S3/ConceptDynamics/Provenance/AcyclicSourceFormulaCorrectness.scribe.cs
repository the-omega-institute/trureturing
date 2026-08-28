using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class AcyclicSourceFormulaCorrectnessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acyclic source formulas hold exactly when a source-supported proof exists.",
        H("Acyclic Source-Formula Correctness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-formula-iff-valid-source-proof"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Provenance/"
                        + "AcyclicSourceFormulaCorrectness."
                        + "source_formula_iff_valid_source_proof"),
                H("Source formulas are correct for valid proofs"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source proof graph extends the existing finite acyclic rank carrier. "
                            + "Each conclusion has an optional direct source and finitely many "
                            + "alternative rules whose premises carry incoming-edge certificates.")),
                    Paragraph(Text(
                        "The Boolean semantics is constructed recursively along the inherited "
                            + "rank. A direct enabled source is one disjunct; each alternative "
                            + "rule is another disjunct whose premises form a conjunction.")),
                    Paragraph(Text(
                        "ValidSourceProof is an independent inductive relation. Well-founded "
                            + "induction proves that the recursive formula holds exactly when a "
                            + "proof uses only the available sources."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("S");
        Formula n = F.Id("n");
        Formula graph = F.Id("G");
        Formula available = F.Id("A");
        Formula conclusion = F.Id("c");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula fin = Call("Fin", n);
        Formula graphType = Call("SourceProofGraph", source, n);
        Formula availableType = Call("Finset", source);
        Formula decidable = Call("DecidableEq", source);
        Formula formula = Call("sourceFormulaHolds", graph, available, conclusion);
        Formula proof = Call("ValidSourceProof", graph, available, conclusion);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(source, type), Comma, Sp,
                OpenBracket, decidable, CloseBracket, Comma, Sp,
                Typed(n, naturals), Comma),
            Seq(
                Typed(graph, graphType), Comma, Sp,
                Typed(available, availableType), Comma, Sp,
                Typed(conclusion, fin), Comma),
            Seq(formula, Sp, Iff, Sp, proof, Dot),
        ]));
    }
}
