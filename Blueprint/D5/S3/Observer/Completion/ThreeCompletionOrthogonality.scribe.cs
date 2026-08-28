using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class ThreeCompletionOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Completion/ThreeCompletionOrthogonality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity, representative normalization, and future behavior are distinct completion "
            + "tasks, with one same-readout implication recorded honestly.",
        H("Three Completion Tasks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-valuations-identify-without-a-generator"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_valuation_identity_without_global_generator"),
                H("Prime valuations can identify an ideal without a global generator"),
                StatementSource.FromAuthor(ValuationGapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over a Dedekind domain with nontrivial class group, the imported prime "
                        + "valuation faithfulness theorem identifies a nonzero ideal supplied "
                        + "by the class group, while nonprincipality excludes every generator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-valuation-generator-gap-disappears-over-the-integers"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "nontrivial_class_group_is_necessary_for_valuation_generator_gap"),
                H("A PID has no valuation-identified nonprincipal witness"),
                StatementSource.FromAuthor(PidDegeneracyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every ideal of the integers is principal. This concrete counterexample "
                        + "shows why the nontrivial-class-group premise is necessary for the "
                        + "first strictness witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("class-group-decision-does-not-choose-a-generator"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "class_group_principality_without_unique_generator"),
                H("Class-group principality does not choose a unique generator"),
                StatementSource.FromAuthor(ClassGroupGapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported integer witnesses one and minus one generate the same nonzero "
                        + "principal ideal. The class-group criterion decides principality, but "
                        + "the ideal equation has more than one generator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("behavior-completion-merges-boolean-microstates"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "future_behavior_quotient_merges_micro_identity"),
                H("A closed behavior quotient can merge microscopic identities"),
                StatementSource.FromAuthor(BehaviorFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite repetition count, including zero, the constant Boolean "
                        + "transcript law factors through the one-point interface. False and "
                        + "true remain distinct states in the same Setoid.ker fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-does-not-imply-normalization"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "identity_completion_does_not_imply_normalization_completion"),
                H("Identity completion does not imply normalization completion"),
                StatementSource.FromAuthor(IdentityNotNormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity readout separates Boolean states, while the indiscriminate "
                        + "Boolean representative relation has two representatives per object."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalization-does-not-imply-identity"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "normalization_completion_does_not_imply_identity_completion"),
                H("Normalization completion does not imply identity completion"),
                StatementSource.FromAuthor(NormalizationNotIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality chooses one Boolean representative for each object, while the "
                        + "constant interface still merges false and true."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalization-does-not-imply-behavior"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "normalization_completion_does_not_imply_behavior_completion"),
                H("Normalization completion does not imply behavior completion"),
                StatementSource.FromAuthor(NormalizationNotBehaviorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Unique equality representatives coexist with a constant readout and an "
                        + "identity-valued future that differs inside its fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("behavior-does-not-imply-identity"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "behavior_completion_does_not_imply_identity_completion"),
                H("Behavior completion does not imply identity completion"),
                StatementSource.FromAuthor(BehaviorNotIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant future is closed on the constant Boolean interface, but that "
                        + "interface does not identify its two microscopic states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("behavior-does-not-imply-normalization"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "behavior_completion_does_not_imply_normalization_completion"),
                H("Behavior completion does not imply normalization completion"),
                StatementSource.FromAuthor(BehaviorNotNormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Constant Boolean behavior closes, while an indiscriminate representative "
                        + "relation still fails uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-readout-identity-implies-behavior"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "same_readout_identity_implies_behavior_completion"),
                H("Identity under one readout implies every deterministic behavior"),
                StatementSource.FromAuthor(IdentityImpliesBehaviorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sixth requested nonimplication direction is false under the formalized "
                        + "same-readout semantics: injectivity turns equal readouts into equal "
                        + "states, so every deterministic future is fiber-constant."))),
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

    private static Formula ValuationGapFormula()
    {
        Formula ring = F.Id("R");
        Formula ideal = F.Id("I");
        return Disp(Seq(
            Call("DedekindDomain", ring), Sp, Land, Sp,
            Call("Nontrivial", Call("ClassGroup", ring)), Sp, Rightarrow, RowBreak,
            Exists, Sp, ideal, Colon, Sp, Call("Ideal", ring), Comma, Sp,
            Call("PrimeValuationIdentityCompletion", ideal), Sp, Land, Sp,
            Neg, Sp, Call("IsPrincipal", ideal), Sp, Land, Sp,
            Neg, Sp, Call("UniqueGenerator", ideal), Dot));
    }

    private static Formula PidDegeneracyFormula()
    {
        Formula ideal = F.Id("I");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        return Disp(Seq(
            Neg, Sp, Exists, Sp, ideal, Colon, Sp, Call("Ideal", integers), Comma, Sp,
            Call("PrimeValuationIdentityCompletion", ideal), Sp, Land, Sp,
            Neg, Sp, Call("IsPrincipal", ideal), Dot));
    }

    private static Formula ClassGroupGapFormula()
    {
        Formula ideal = F.Id("I");
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        return Disp(Seq(
            Exists, Sp, ideal, Colon, Sp, Call("Ideal", integers), Comma, Sp,
            Call("ClassGroupPrincipalityDecision", ideal), Sp, Land, Sp,
            Call("IsPrincipal", ideal), Sp, Land, Sp,
            Neg, Sp, Call("UniqueGenerator", ideal), Dot));
    }

    private static Formula BehaviorFiberFormula()
    {
        Formula sampleCount = F.Id("n");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula quotient = F.Id("qBool");
        Formula transcript = Call("iidTranscript", sampleCount);
        return Disp(Seq(
            Forall, Sp, sampleCount, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Call("FactorsThrough", quotient, transcript), Sp, Land, RowBreak,
            Call("BehaviorCompletion", quotient, transcript), Sp, Land, RowBreak,
            Exists, Sp, x, Comma, Sp, y, InMacro, Sp, F.Id("Bool"), Comma, Sp,
            x, Sp, Neq, Sp, y, Sp, Land, Sp,
            Call("ker", quotient, x, y), Dot));
    }

    private static Formula IdentityNotNormalizationFormula() => Disp(Seq(
        Call("IdentityCompletion", F.Id("idBool")), Sp, Land, Sp,
        Neg, Sp, Call("NormalizationCompletion", F.Id("trueBoolRelation")), Dot));

    private static Formula NormalizationNotIdentityFormula() => Disp(Seq(
        Call("NormalizationCompletion", F.Id("equalityBoolRelation")), Sp, Land, Sp,
        Neg, Sp, Call("IdentityCompletion", F.Id("constantBoolInterface")), Dot));

    private static Formula NormalizationNotBehaviorFormula() => Disp(Seq(
        Call("NormalizationCompletion", F.Id("equalityBoolRelation")), Sp, Land, Sp,
        Neg, Sp, Call("BehaviorCompletion", F.Id("constantBoolInterface"),
            F.Id("identityBoolFuture")), Dot));

    private static Formula BehaviorNotIdentityFormula() => Disp(Seq(
        Call("BehaviorCompletion", F.Id("constantBoolInterface"),
            F.Id("constantFuture")), Sp, Land, Sp,
        Neg, Sp, Call("IdentityCompletion", F.Id("constantBoolInterface")), Dot));

    private static Formula BehaviorNotNormalizationFormula() => Disp(Seq(
        Call("BehaviorCompletion", F.Id("constantBoolInterface"),
            F.Id("constantFuture")), Sp, Land, Sp,
        Neg, Sp, Call("NormalizationCompletion", F.Id("trueBoolRelation")), Dot));

    private static Formula IdentityImpliesBehaviorFormula()
    {
        Formula readout = F.Id("q");
        Formula future = F.Id("f");
        return Disp(Seq(
            Forall, Sp, readout, Comma, Sp, future, Comma, Sp,
            Call("IdentityCompletion", readout), Sp, Rightarrow, Sp,
            Call("BehaviorCompletion", readout, future), Dot));
    }
}
