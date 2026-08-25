using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class ExternalizedCertificationMeaningDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One realized decision transcript can carry collapsed or independently sampled "
            + "certification value.",
        H("Externalized Certification Meaning"),
        Blocks(Describe.Lean(
            DescribeId.Create("externalized-certification-meaning"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Interpretation/ExternalizedCertificationMeaning."
                    + "externalized_certification_meaning"),
            H("Certification meaning is external to the decision transcript"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The implementation is the constant-false Boolean program and the expected "
                        + "behavior is the identity. The constructed deployment law gives the "
                        + "single failing input mass (1 + epsilon)/2, strictly above epsilon.")),
                Paragraph(Text(
                    "Both worlds realize the same all-false suite and therefore the same "
                        + "all-green bit transcript. In the co-selected world every coordinate "
                        + "law is concentrated on that realized input. In the independent world "
                        + "every coordinate law equals the deployment law.")),
                Paragraph(Text(
                    "The bad-green mass is the product of the coordinate pass masses. It is one "
                        + "under co-selection and ((1 - epsilon)/2)^m under independent sampling. "
                        + "The repository exponential bound gives the displayed certification "
                        + "envelope, while positivity of epsilon and m makes the co-selected mass "
                        + "strictly exceed that envelope.")),
                Paragraph(Text(
                    "The final two clauses state the information-theoretic corollary directly: "
                        + "neither bad-green mass nor the independent-sampling precondition factors "
                        + "through the transcript. The source explicitly leaves signature semantics "
                        + "out of scope, so no separate universal semantics of signing is invented."))),
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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula epsilon = F.Id("epsilon");
        Formula budget = F.Id("m");
        Formula deployment = Mu;
        Formula coSelected = new Formula.Subscript(F.Id("W"), F.Id("c"));
        Formula independent = new Formula.Subscript(F.Id("W"), F.Id("i"));
        Formula index = F.Id("j");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolType = F.Id("Bool");
        Formula pmfBool = Call("PMF", boolType);
        Formula world = Call("World", budget);
        Formula suite = Seq(Operatorname, Grp(F.Id("suite")));
        Formula transcript = Seq(Operatorname, Grp(F.Id("Transcript")));
        Formula badGreen = Seq(Operatorname, Grp(F.Id("BadGreenMass")));
        Formula loss = Call("Loss", F.Id("constantFalse"), F.Id("id"), deployment);
        Formula suiteCo = Apply(suite, coSelected);
        Formula suiteIndependent = Apply(suite, independent);
        Formula independentRate = new Formula.Fraction(
            Seq(D(1), Minus, epsilon), D(2));
        Formula independentMass = new Formula.Power(
            Seq(independentRate), Seq(budget));
        Formula envelope = Call(
            "exp", Seq(Minus, epsilon, Sp, Times, Sp, budget));
        Formula factorsMass = Call("FactorsThrough", badGreen, transcript);
        Formula independentPredicate = Call("IndependentOf", deployment);
        Formula factorsIndependence =
            Call("FactorsThrough", independentPredicate, transcript);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, epsilon, Colon, Sp, real, Comma, Sp,
            budget, Colon, Sp, natural, Comma, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, epsilon, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, budget, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, deployment, Colon, Sp, pmfBool, Comma, Sp,
            coSelected, Comma, Sp, independent, Colon, Sp, world, Comma,
            RowBreak, Grp(),
            suiteCo, Sp, Eq, Sp, suiteIndependent, Sp, Land, RowBreak, Grp(),
            Forall, Sp, index, Comma, Sp,
            Apply(suiteCo, index), Sp, Eq, Sp, F.Id("false"), Sp, Land,
            RowBreak, Grp(),
            Apply(transcript, coSelected), Sp, Eq, Sp,
            Apply(transcript, independent), Sp, Land, RowBreak, Grp(),
            Forall, Sp, index, Comma, Sp,
            Call("law", coSelected, index), Sp, Eq, Sp,
            Call("pure", Apply(suiteCo, index)), Sp, Land, RowBreak, Grp(),
            Forall, Sp, index, Comma, Sp,
            Call("law", independent, index), Sp, Eq, Sp,
            deployment, Sp, Land, RowBreak, Grp(),
            loss, Sp, Eq, Sp,
            new Formula.Fraction(Seq(D(1), Plus, epsilon), D(2)), Sp, Land,
            RowBreak, Grp(),
            epsilon, Sp, Lt, Sp, loss, Sp, Land, RowBreak, Grp(),
            Apply(badGreen, coSelected), Sp, Eq, Sp, D(1), Sp, Land,
            RowBreak, Grp(),
            Apply(badGreen, independent), Sp, Eq, Sp,
            independentMass, Sp, Land, RowBreak, Grp(),
            Apply(badGreen, independent), Sp, Leq, Sp,
            envelope, Sp, Land, RowBreak, Grp(),
            envelope, Sp, Lt, Sp, Apply(badGreen, coSelected), Sp, Land,
            RowBreak, Grp(),
            Call("laws", coSelected), Sp, Neq, Sp,
            Call("laws", independent), Sp, Land, RowBreak, Grp(),
            Neg, Sp, factorsMass, Sp, Land, RowBreak, Grp(),
            Neg, Sp, factorsIndependence, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
