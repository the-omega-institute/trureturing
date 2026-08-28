using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class SemanticClosureStrictNoveltyCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
            + "SemanticClosureStrictNoveltyCriterion."
            + "semantic_closure_strict_novelty_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict common-kernel refinement is exactly escape from semantic closure.",
        H("Semantic Closure Strict Novelty Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-closure-strict-novelty-criterion"),
            DeclarationHandle.Create(Declaration),
            H("A candidate is strictly novel exactly when it splits an old kernel pair"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Gamma is an arbitrary family of output-valued concepts on X. The old "
                        + "and extended common kernels are the canonical jointKernel objects, "
                        + "with the candidate inserted into the same family.")),
                Paragraph(Text(
                    "The extended kernel is always contained in the old kernel. The inclusion "
                        + "is strict exactly when the frozen zero-gain equality criterion fails, "
                        + "equivalently when the candidate is outside SemanticClosure Gamma."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula family = Gamma;
        Formula candidate = F.Id("p");
        Formula definition = F.Id("d");
        Formula concept = Call("Concept", state, output);
        Formula inserted = Call("insert", candidate, family);
        Formula readout = Call("readout", definition);
        Formula oldKernel = Call(
            "jointKernel",
            Seq(LambdaLower, Sp, definition, Colon, Sp, family, Comma, Sp, readout));
        Formula extendedKernel = Call(
            "jointKernel",
            Seq(LambdaLower, Sp, definition, Colon, Sp, inserted, Comma, Sp, readout));
        Formula strict = Call("StrictSubset", extendedKernel, oldKernel);
        Formula outside = Seq(
            Neg, Open, candidate, Sp, InMacro, Sp,
            Call("SemanticClosure", family), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            family, Colon, Sp, Call("Set", concept), Comma, Sp,
            candidate, Colon, Sp, concept, Comma, RowBreak, Grp(),
            strict, Sp, Leftrightarrow, Sp, outside, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
