using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class StrictKernelNoveltyCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict kernel shrinkage is exactly semantic novelty of the added readout.",
        H("Strict Kernel Novelty Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-kernel-novelty-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                        + "StrictKernelNoveltyCriterion.strict_kernel_novelty_criterion"),
                H("A readout is novel exactly when it splits an old kernel pair"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Gamma is an output-valued concept family on X, and p is a candidate "
                            + "concept on the same carrier. SemanticClosure and jointKernel are "
                            + "the canonical imported objects.")),
                    Paragraph(Text(
                        "The inserted-family kernel is always contained in the original kernel. "
                            + "The frozen zero-gain criterion identifies equality with closure "
                            + "membership, so inequality is exactly strict shrinkage."))),
                DescribeRole.Theorem))));

    private static Formula Type() =>
        Seq(Operatorname, Grp(F.Id("Type")));

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

    private static Formula CriterionFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula family = Gamma;
        Formula candidate = F.Id("p");
        Formula definition = F.Id("d");
        Formula concept = Call("Concept", state, output);
        Formula familyType = Call("Set", concept);
        Formula inserted = Call("insert", candidate, family);
        Formula readout = Call("readout", definition);
        Formula oldKernel = Call(
            "jointKernel",
            Seq(LambdaLower, Sp, definition, Colon, Sp, family, Comma, Sp, readout));
        Formula extendedKernel = Call(
            "jointKernel",
            Seq(LambdaLower, Sp, definition, Colon, Sp, inserted, Comma, Sp, readout));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, Type(), Comma,
            RowBreak, Grp(),
            family, Colon, Sp, familyType, Comma, Sp,
            candidate, Colon, Sp, concept, Comma,
            RowBreak, Grp(),
            Call("StrictSubset", extendedKernel, oldKernel), Sp, Leftrightarrow,
            RowBreak, Grp(),
            Neg, Open, candidate, Sp, InMacro, Sp,
            Call("SemanticClosure", family), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
