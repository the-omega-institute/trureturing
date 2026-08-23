using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class TranslationLossMonotonicityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic postprocessing preserves target defects and cannot reduce target loss.",
        H("Translation Loss under Postprocessing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("readout-target-law"),
                DeclarationHandle.Create(DeclarationPrefix + "readoutTargetLaw"),
                H("Joint readout-target law"),
                StatementSource.FromAuthor(ReadoutTargetLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Push the finite state law through the paired map x maps to (q(x), T(x)). "
                        + "This directly constructs the joint law used by the source's "
                        + "conditional target entropy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("target-residual-entropy"),
                DeclarationHandle.Create(DeclarationPrefix + "targetResidualEntropy"),
                H("Target residual entropy"),
                StatementSource.FromAuthor(TargetResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Target residual entropy is the finite conditional entropy of T(X) after "
                        + "the readout q(X), evaluated on the constructed paired pushforward law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("translation-loss-monotone-under-postprocessing"),
                DeclarationHandle.Create(DeclarationPrefix + "translation_loss_monotone"),
                H("Translation loss is monotone under postprocessing"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let h be a finite readout, g a deterministic postprocessor, T a target, "
                            + "and mu a normalized nonnegative state law. The defect relation is "
                            + "the canonical set of state pairs merged by a readout but separated "
                            + "by T.")),
                    Paragraph(Text(
                        "Applying g to equal h-values proves the first public inclusion directly. "
                            + "Thus every target distinction already lost by h remains lost after "
                            + "the translation chain.")),
                    Paragraph(Text(
                        "For the second public conjunct, the proof constructs the deterministic "
                            + "Markov chain T(X), h(X), g(h(X)) and directly applies the accepted "
                            + "data-processing theorem. Entropy-chain and mutual-information "
                            + "identities convert that bound to the displayed conditional-target "
                            + "entropy inequality."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

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

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, carrier, Close, CloseBracket);

    private static Formula ReadoutTargetLawFormula()
    {
        Formula state = F.Id("X");
        Formula readoutCarrier = F.Id("B");
        Formula targetCarrier = F.Id("A");
        Formula mu = Mu;
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula x = F.Id("x");

        return Disp(Seq(
            Call("readoutTargetLaw", mu, readout, target), Sp, Eq, Sp,
            Call("pushforward", mu,
                Seq(x, Sp, Mapsto, Sp,
                    Open, Apply(readout, x), Comma, Sp, Apply(target, x), Close)), Dot));
    }

    private static Formula TargetResidualFormula()
    {
        Formula mu = Mu;
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        return Disp(Seq(
            Call("targetResidualEntropy", mu, readout, target), Sp, Eq, Sp,
            Call("conditionalEntropy", Call("readoutTargetLaw", mu, readout, target)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula fineCarrier = F.Id("Y");
        Formula coarseCarrier = F.Id("W");
        Formula targetCarrier = F.Id("Z");
        Formula mu = Mu;
        Formula x = F.Id("x");
        Formula fine = F.Id("h");
        Formula postprocess = F.Id("g");
        Formula target = F.Id("T");
        Formula coarse = Seq(postprocess, Sp, Circ, Sp, fine);
        Formula probabilityLaw = Seq(
            Open, Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mu, x), Close,
            Sp, Land, Sp, Sum, Underscore, Grp(x), Sp,
            Apply(mu, x), Sp, Eq, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, fineCarrier, Comma, Sp,
            coarseCarrier, Comma, Sp, targetCarrier, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Fintype(state), Comma, Sp, Fintype(fineCarrier), Comma, Sp,
            Fintype(coarseCarrier), Comma, Sp, Fintype(targetCarrier), Comma,
            RowBreak, Grp(),
            mu, Colon, Sp, Arrow(state, Seq(Mathbb, Grp(F.Id("R")))), Comma, Sp,
            probabilityLaw, Comma, RowBreak, Grp(),
            fine, Colon, Sp, Arrow(state, fineCarrier), Comma, Sp,
            postprocess, Colon, Sp, Arrow(fineCarrier, coarseCarrier), Comma, Sp,
            target, Colon, Sp, Arrow(state, targetCarrier), Comma, RowBreak, Grp(),
            Call("defectRelation", fine, target), Sp, Subseteq, Sp,
            Call("defectRelation", coarse, target), Sp, Land, RowBreak, Grp(),
            Call("targetResidualEntropy", mu, fine, target), Sp, Leq, Sp,
            Call("targetResidualEntropy", mu, coarse, target), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
