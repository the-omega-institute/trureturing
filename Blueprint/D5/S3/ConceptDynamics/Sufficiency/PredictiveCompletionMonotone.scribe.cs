using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class PredictiveCompletionMonotoneDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/PredictiveCompletionMonotone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive completion preserves the refinement order of readouts.",
        H("Predictive Completion Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("predictive-completion-preserves-refinement"),
                DeclarationHandle.Create(DeclarationPrefix + "predictive_completion_monotone"),
                H("Predictive completion preserves refinement"),
                StatementSource.FromAuthor(MonotoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The premise says that equality under the finer readout r implies "
                            + "equality under q. This is exactly inclusion of the two current "
                            + "readout kernels.")),
                    Paragraph(Text(
                        "The all-iterate congruence kernel is monotone under relation inclusion. "
                            + "Quotient equality for r therefore yields the corresponding kernel "
                            + "relation for q, and the quotient soundness theorem concludes.")),
                    Paragraph(Text(
                        "No inhabitedness, finiteness, or update assumptions are used; the "
                            + "empty, singleton, constant-update, identity-readout, and zero-step "
                            + "examples are checked in the Lean module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refinement-premise-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "refinement_hypothesis_is_necessary"),
                H("The refinement premise is necessary"),
                StatementSource.FromAuthor(NecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On Bool states with identity dynamics, a constant Unit readout makes "
                            + "the two quotient classes equal, while the identity Bool readout "
                            + "keeps true and false distinct.")),
                    Paragraph(Text(
                        "Thus the conclusion fails when the relation-inclusion premise is removed. "
                            + "This concrete counterexample is the required audit of the only "
                            + "non-definitional hypothesis."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula MonotoneFormula()
    {
        Formula state = F.Id("X");
        Formula coarseOutput = F.Id("O");
        Formula fineOutput = F.Id("P");
        Formula update = F.Id("F");
        Formula coarse = F.Id("q");
        Formula fine = F.Id("r");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula projectionCoarse = Apply(F.Id("predictiveProjection"), update, coarse);
        Formula projectionFine = Apply(F.Id("predictiveProjection"), update, fine);
        Formula premise = Seq(
            Apply(fine, first), Sp, Eq, Sp, Apply(fine, second), Sp,
            Rightarrow, Sp, Apply(coarse, first), Sp, Eq, Sp, Apply(coarse, second));
        Formula conclusion = Seq(
            Apply(projectionFine, first), Sp, Eq, Sp, Apply(projectionFine, second), Sp,
            Rightarrow, Sp, Apply(projectionCoarse, first), Sp, Eq, Sp,
            Apply(projectionCoarse, second));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, coarseOutput, Comma, Sp, fineOutput), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(coarse, Arrow(state, coarseOutput)), Comma, Sp,
            Typed(fine, Arrow(state, fineOutput)), Comma, RowBreak, Grp(),
            Open, Forall, Sp, Typed(Seq(first, Comma, Sp, second), state), Comma, Sp,
            Open, premise, Close, Sp, Land, Sp,
            Open, conclusion, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NecessaryFormula()
    {
        Formula state = F.Id("Bool");
        Formula update = F.Id("id");
        Formula constant = Seq(Operatorname, Grp(F.Id("const")), Open, F.Id("Unit"), Close);
        Formula identity = F.Id("id");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula constantProjection = Apply(F.Id("predictiveProjection"), update, constant);
        Formula identityProjection = Apply(F.Id("predictiveProjection"), update, identity);
        Formula implication = Seq(
            Apply(constantProjection, x), Sp, Eq, Sp, Apply(constantProjection, y), Sp,
            Rightarrow, Sp, Apply(identityProjection, x), Sp, Eq, Sp,
            Apply(identityProjection, y));

        return Disp(Seq(
            Neg, Sp, Forall, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            implication, Dot));
    }
}
