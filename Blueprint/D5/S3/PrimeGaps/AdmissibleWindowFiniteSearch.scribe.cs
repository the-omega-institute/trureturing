using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class AdmissibleWindowFiniteSearchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound and complete normalized even search.",
        H("Sound and complete normalized even search"),
        Blocks(Describe.Lean(
            DescribeId.Create("admissible-window-finite-search"),
            DeclarationHandle.Create("D5/S3/PrimeGaps/AdmissibleWindowFiniteSearch.admissibleWindowCheck_eq_true_iff"),
            H("Sound and complete normalized even search"),
            StatementSource.FromAuthor(F.Disp(
                F.Seq(F.Forall, F.Sp, F.Id("k"), F.Comma, F.Id("B"), F.InMacro, F.Sp, F.Id("Nat"), F.Comma, F.D(0), F.Lt, F.Id("k"), F.Rightarrow, F.Grp(Call("admissibleWindowCheck", F.Id("k"), F.Id("B")), F.Eq, F.Id("true"), F.Iff, F.Sp, Call("AdmissibleWindowWitness", F.Id("k"), F.Id("B")))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every positive natural tuple size k and every natural width B, the finite Boolean search succeeds exactly when the existing all-prime admissible-window proposition holds. Completeness subtracts the minimum offset, preserves cardinality and omitted residues, and proves that a normalized admissible tuple is even. Soundness uses the imported finite prime-cutoff theorem. The result concerns standard admissible-tuple optimization and claims formalization content, not new number theory."))),
            DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
