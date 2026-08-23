using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class DistributionIndependentClosureDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distribution-independent readout closure is equivalent to deterministic depth-zero closure.",
        H("Distribution-Independent Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distribution-independent-closure-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/DistributionIndependentClosure."
                        + "distribution_independent_closure_criterion"),
                H("Distribution-independent closure criterion"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a nonempty finite state carrier, let tau update its states, "
                            + "and let q map Y surjectively onto the actual readout carrier O. "
                            + "A kernel is effective when it advances the q-pushforward of every "
                            + "initial probability mass exactly as q after tau does.")),
                    Paragraph(Text(
                        "An effective kernel exists exactly when q is a deterministic factor: "
                            + "there is a readout update sigma satisfying q(tau(y)) = sigma(q(y)) "
                            + "for every state. This is also equivalent to equality of the "
                            + "depth-zero and depth-one future-word relations, hence to the "
                            + "existing least stability depth being zero.")),
                    Paragraph(Text(
                        "Applying the evolution law to point masses makes each kernel row at q(y) "
                            + "the point mass at q(tau(y)). Surjectivity reaches every readout, so "
                            + "the factor update associated with an effective kernel is unique, "
                            + "every effective kernel is deterministic on every readout, and the "
                            + "effective kernel itself is unique whenever one exists.")),
                    Paragraph(Text(
                        "The proof imports the observer family's canonical future-word stability "
                            + "depth and uses Mathlib probability mass map and bind laws. No "
                            + "duplicate future relation, depth, or determinism-by-definition is "
                            + "introduced."))),
                DescribeRole.Theorem))));

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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula CriterionFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula kernel = F.Id("K");
        Formula factorUpdate = Sigma;
        Formula initial = Mu;
        Formula statePoint = F.Id("y");
        Formula outputPoint = F.Id("o");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula pmf = Seq(Operatorname, Grp(F.Id("PMF")));
        Formula pmfState = Apply(pmf, state);
        Formula pmfOutput = Apply(pmf, output);
        Formula kernelType = Arrow(output, pmfOutput);
        Formula effective = Apply(Seq(Operatorname, Grp(F.Id("Eff"))), kernel);
        Formula factor = Apply(Seq(Operatorname, Grp(F.Id("Fac"))), factorUpdate);
        Formula pushUpdate = Seq(update, Underscore, Grp(Star));
        Formula pushReadout = Seq(readout, Underscore, Grp(Star));
        Formula pushKernel = Seq(kernel, Underscore, Grp(Star));
        Formula stabilityDepth = Apply(
            Seq(Operatorname, Grp(F.Id("observationStabilityDepth"))), update, readout);
        Formula effectiveDefinition = Seq(
            Open, Forall, Sp, kernel, Colon, Sp, kernelType, Comma, Sp,
            effective, Sp, Iff, Sp,
            Open, Forall, Sp, initial, Colon, Sp, pmfState, Comma, Sp,
            Apply(pushReadout, Apply(pushUpdate, initial)), Sp, Eq, Sp,
            Apply(pushKernel, Apply(pushReadout, initial)), Close, Close);
        Formula factorDefinition = Seq(
            Open, Forall, Sp, factorUpdate, Colon, Sp, Arrow(output, output), Comma, Sp,
            factor, Sp, Iff, Sp,
            Open, Forall, Sp, statePoint, Colon, Sp, state, Comma, Sp,
            Apply(readout, Apply(update, statePoint)), Sp, Eq, Sp,
            Apply(factorUpdate, Apply(readout, statePoint)), Close, Close);
        Formula existsKernel = Seq(Exists, Sp, kernel, Colon, Sp, kernelType,
            Comma, Sp, effective);
        Formula existsFactor = Seq(Exists, Sp, factorUpdate, Colon, Sp,
            Arrow(output, output), Comma, Sp, factor);
        Formula deterministicRow = Seq(
            Forall, Sp, outputPoint, Colon, Sp, output, Comma, Sp,
            Apply(kernel, outputPoint), Sp, Eq, Sp,
            new Formula.Subscript(DeltaLower, Apply(factorUpdate, outputPoint)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, type, Comma, Sp,
            output, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, state,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, state,
            CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, Arrow(state, state), Comma, Sp,
            readout, Colon, Sp, Arrow(state, output), Comma, Sp,
            Operatorname, Grp(F.Id("Surjective")), Open, readout, Close,
            Comma, RowBreak, Grp(),
            effectiveDefinition, Comma, RowBreak, Grp(),
            factorDefinition, Comma, RowBreak, Grp(),
            Open, existsKernel, Sp, Iff, Sp, existsFactor, Close, Sp, Land, RowBreak, Grp(),
            Open, existsFactor, Sp, Iff, Sp, stabilityDepth, Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, kernel, Colon, Sp, kernelType, Comma, Sp,
            effective, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, factorUpdate, Colon, Sp, Arrow(output, output),
            Comma, Sp, factor, Sp, Land, Sp, deterministicRow, Close,
            Sp, Land, RowBreak, Grp(),
            Open, existsKernel, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, kernel, Colon, Sp, kernelType, Comma, Sp,
            effective, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
