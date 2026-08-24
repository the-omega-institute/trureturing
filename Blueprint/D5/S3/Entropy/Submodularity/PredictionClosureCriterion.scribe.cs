using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class PredictionClosureCriterionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Submodularity/PredictionClosureCriterion."
            + "prediction_closure_iff_markov";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A deterministic finite interface is predictively closed exactly when past and future "
            + "factor conditionally on every active interface value.",
        H("Prediction Closure Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("prediction-closure-is-conditional-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Prediction closure is conditional factorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let P be the complete finite past, F the finite future, and C a finite "
                        + "current interface. The public graph-support hypothesis states that "
                        + "every nonzero cell has C equal to the supplied deterministic readout "
                        + "q of P. The joint mass function is nonnegative and normalized.")),
                Paragraph(Text(
                    "The predictive-closure defect is constructed as the repository conditional "
                        + "mutual information of the law on C times (P times F). It vanishes "
                        + "exactly when, for every C-value of nonzero marginal mass, the "
                        + "conditional joint law of P and F is the product of its own marginals. "
                        + "This is the finite Markov-chain condition from past through the "
                        + "current interface to future.")),
                Paragraph(Text(
                    "The proof directly applies the frozen zero conditional-mutual-information "
                        + "characterization. That imported result is stronger than needed because "
                        + "conditional factorization does not require the interface to be a "
                        + "deterministic readout, but the source restriction remains public."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Entropy/Submodularity/MarkovDataProcessing"))]));

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula pastCarrier = F.Id("P");
        Formula currentCarrier = F.Id("C");
        Formula futureCarrier = F.Id("F");
        Formula past = F.Id("u");
        Formula current = F.Id("c");
        Formula future = F.Id("v");
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula cell = Seq(p, Open, current, Comma, Sp,
            Open, past, Comma, Sp, future, Close, Close);
        Formula law = Seq(
            Open, Forall, Sp, F.Id("x"), Comma, Sp, D(0), Sp, Leq, Sp,
            p, Open, F.Id("x"), Close, Close, Sp, Land, Sp,
            Sum, Underscore, Grp(F.Id("x")), Sp, p, Open, F.Id("x"), Close,
            Sp, Eq, Sp, D(1));
        Formula graphSupport = Seq(
            Forall, Sp, current, Comma, Sp, past, Comma, Sp, future, Comma, Sp,
            cell, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            current, Sp, Eq, Sp, q, Open, past, Close);
        Formula currentMass = Seq(p, Underscore, Grp(currentCarrier), Open, current, Close);
        Formula conditionalJoint = Seq(
            p, Underscore,
            Grp(pastCarrier, futureCarrier, Sp, Mid, Sp, current),
            Open, past, Comma, Sp, future, Close);
        Formula conditionalPast = Seq(
            p, Underscore, Grp(pastCarrier, Sp, Mid, Sp, current),
            Open, past, Close);
        Formula conditionalFuture = Seq(
            p, Underscore, Grp(futureCarrier, Sp, Mid, Sp, current),
            Open, future, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, pastCarrier, Comma, Sp, currentCarrier, Comma, Sp,
            futureCarrier, Comma, RowBreak, Grp(),
            Fintype(pastCarrier), Sp, Fintype(currentCarrier), Sp,
            Fintype(futureCarrier), Comma, RowBreak, Grp(),
            q, Colon, Sp, pastCarrier, Sp, To, Sp, currentCarrier, Comma, Sp,
            p, Colon, Sp, currentCarrier, Sp, Times, Sp,
            Open, pastCarrier, Sp, Times, Sp, futureCarrier, Close,
            Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            Open, law, Sp, Land, Sp, graphSupport, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("conditionalMutualInformation", p), Sp, Eq, Sp, D(0),
            Sp, Iff, Sp, RowBreak, Grp(),
            Forall, Sp, current, Comma, Sp, currentMass, Sp, Neq, Sp, D(0),
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            Forall, Sp, past, Comma, Sp, future, Comma, Sp,
            conditionalJoint, Sp, Eq, Sp,
            conditionalPast, Sp, Cdot, Sp, conditionalFuture, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
