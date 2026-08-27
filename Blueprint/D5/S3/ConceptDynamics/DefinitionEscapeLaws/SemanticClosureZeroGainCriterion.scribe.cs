using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class SemanticClosureZeroGainCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic closure is exactly preservation of the common observational kernel.",
        H("Semantic Closure Zero-Gain Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("semantic-closure-zero-gain-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                        + "SemanticClosureZeroGainCriterion."
                        + "semantic_closure_zero_gain_criterion"),
                H("A candidate has zero gain exactly when the common kernel is unchanged"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Gamma is a family of output-valued concepts on X, and p is a "
                            + "candidate concept on the same carrier. SemanticClosure and "
                            + "jointKernel are imported from the canonical definition-kernel "
                            + "family.")),
                    Paragraph(Text(
                        "If p is constant on Gamma's common kernel, the extra inserted "
                            + "coordinate cannot split any old kernel pair. Conversely, equality "
                            + "of the inserted and old kernels forces p to agree on every old "
                            + "kernel pair."))),
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
            candidate, Sp, InMacro, Sp, Call("SemanticClosure", family),
            Sp, Leftrightarrow,
            RowBreak, Grp(),
            extendedKernel, Sp, Eq, Sp, oldKernel, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
