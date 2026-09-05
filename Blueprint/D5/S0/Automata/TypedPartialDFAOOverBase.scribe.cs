using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class TypedPartialDFAOOverBaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed partial DFAOs preserve an underlying numeration "
            + "automaton and separate global correctness from finite-prefix "
            + "fitting.",
        H("Typed Partial DFAOs over a Numeration Base"),
        Blocks(Describe.Lean(
            DescribeId.Create("global-model-implies-prefix-model"),
            DeclarationHandle.Create(
                "D5/S0/Automata/TypedPartialDFAOOverBase.sparse_global_model_implies_prefix_model"),
            H("Every bounded global model fits every finite prefix"),
            StatementSource.FromAuthor(PrefixModelFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The base automaton owns legality, while every defined DFAO transition projects to a legal base transition. Sparse correctness is stated independently from finite-prefix fitting.")),
                Paragraph(Text(
                    "The theorem is the logical direction required by finite UNSAT certificates: any globally correct bounded-state machine would also be a model of every genuine finite prefix."))),
            DescribeRole.Theorem)),
        []));

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

    private static Formula PrefixModelFormula() => Disp(Seq(
        Call("HasGlobalModelAtMost", F.Id("P"), F.Id("k")),
        Sp, Implies, Sp,
        Call("HasPrefixModelAtMost", F.Id("P"), F.Id("N"), F.Id("k"))));
}
