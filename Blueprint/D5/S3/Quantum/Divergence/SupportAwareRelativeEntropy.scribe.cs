using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SupportAwareRelativeEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantum trace-log relative entropy is extended by top exactly "
            + "outside support inclusion.",
        H("Support-Aware Quantum Relative Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("extended-relative-entropy-top-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_top_iff"),
                H("The infinite branch is exactly support failure"),
                StatementSource.FromAuthor(TopCharacterizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Support containment is frozen as reverse inclusion of matrix nullspaces: every vector annihilated by the second state is annihilated by the first.")),
                    Paragraph(Text(
                        "The extended entropy takes values in the reals with top adjoined. On supported pairs it is the finite trace-log branch; outside support inclusion it is exactly top.")),
                    Paragraph(Text(
                        "Positivity, data-processing, and Petz equality are deliberately left as separate future theorems on this carrier."))),
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

    private static Formula TopCharacterizationFormula() => Disp(Seq(
        Call("extendedQuantumRelativeEntropy", Rho, SigmaLower),
        Sp, Eq, Sp, Infty,
        Sp, Iff, Sp, Neg,
        Call("SupportContained", Rho, SigmaLower)));
}
