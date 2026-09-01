using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LRATUnsatisfiableDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Certificates/LRATUnsatisfiable.empty_clause_proof_iff_unsatisfiable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathlib LRAT empty-clause proofs are exactly propositional "
            + "unsatisfiability certificates.",
        H("LRAT Refutations and Unsatisfiability"),
        Blocks(Describe.Lean(
            DescribeId.Create("lrat-unsatisfiable"),
            DeclarationHandle.Create(Declaration),
            H("Empty-clause derivability is equivalent to unsatisfiability"),
            StatementSource.FromAuthor(EquivalenceFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Pinned Mathlib's lrat_proof command constructs kernel-checked proof terms in the Sat.Fmla.proof semantics.")),
                Paragraph(Text(
                    "For the empty clause, that proof target reduces exactly to the assertion that every valuation satisfying the input formula yields false.")),
                Paragraph(Text(
                    "The repository wrapper therefore adds no second checker. It gives later SAT-backed open-problem lanes one named soundness boundary for imported LRAT certificates."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula EquivalenceFormula() => Disp(Seq(
        Forall, Sp, F.Id("F"), Comma, Sp,
        Call("proof", F.Id("F"), Seq(OpenBracket, CloseBracket)),
        Sp, Iff, Sp,
        Call("Unsatisfiable", F.Id("F")), Dot));

}
