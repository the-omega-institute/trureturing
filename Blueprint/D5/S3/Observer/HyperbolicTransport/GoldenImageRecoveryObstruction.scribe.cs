using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HyperbolicTransport;

internal sealed class GoldenImageRecoveryObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/HyperbolicTransport/GoldenImageRecoveryObstruction."
            + "golden_image_recovery_obstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The projective golden boundary image forgets every observer rapidity.",
        H("Golden Image Recovery Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-image-recovery-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("A fixed projective boundary image cannot reconstruct the observer"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observer event and its genuine tangent are the canonical objects "
                        + "constructed by the preceding null-direction theorem. The boundary "
                        + "projection is defined on their concrete orbit and sends each state's "
                        + "sum and difference to Mathlib's projective quotient.")),
                Paragraph(Text(
                    "Positive rapidity-dependent amplitudes disappear in projective space, "
                        + "so every rapidity has the same ordered pair of golden null points. "
                        + "The event-tangent states themselves remain distinct.")),
                Paragraph(Text(
                    "The theorem states the resulting non-injectivity directly and rules out "
                        + "both a rapidity decoder and a concrete observer-state decoder from "
                        + "the complete boundary image."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula vector = Call("Prod", real, real);
        Formula projectivePoint = Call("Projectivization", real, vector);
        Formula boundaryType = Call("Prod", projectivePoint, projectivePoint);
        Formula observerStateType = Call("Prod", vector, vector);
        Formula type = F.Id("Type");
        Formula eta = F.Id("eta");
        Formula eta1 = F.Id("eta1");
        Formula eta2 = F.Id("eta2");
        Formula state = F.Id("state");
        Formula observerOrbit = F.Id("ObserverOrbit");
        Formula futurePoint = F.Id("futurePoint");
        Formula pastPoint = F.Id("pastPoint");
        Formula boundaryProjection = F.Id("Pi");
        Formula boundaryImage = F.Id("image");
        Formula recoverRapidity = F.Id("recoverRapidity");
        Formula recoverObserver = F.Id("recoverObserver");
        Formula phiPrime = Seq(Varphi, Apos);

        Formula Event(Formula rapidity) => Call("h", rapidity);
        Formula Tangent(Formula rapidity) => Call("tangent", rapidity);
        Formula ObserverState(Formula rapidity) =>
            Call("pair", Event(rapidity), Tangent(rapidity));
        Formula BoundaryImage(Formula rapidity) => Apply(boundaryImage, rapidity);

        Formula observerOrbitDefinition = Call(
            "Subtype",
            Call("range", Lambda(eta, real, ObserverState(eta))));
        Formula boundaryProjectionDefinition = Lambda(
            state,
            observerOrbit,
            Call(
                "pair",
                Call("class", Add(Call("fst", state), Call("snd", state))),
                Call("class", Subtract(Call("snd", state), Call("fst", state)))));
        Formula boundaryImageDefinition = Lambda(
            eta,
            real,
            Apply(boundaryProjection, ObserverState(eta)));
        Formula fixedImage = ForAll(
            [Bound("eta", real)],
            Equal(
                BoundaryImage(eta),
                Call("pair", futurePoint, pastPoint)));
        Formula distinctFibers = ForAll(
            [Bound("eta1", real), Bound("eta2", real)],
            Implies(
                NotEqual(eta1, eta2),
                And(
                    Equal(BoundaryImage(eta1), BoundaryImage(eta2)),
                    NotEqual(ObserverState(eta1), ObserverState(eta2)))));
        Formula noRapidityDecoder = ForAll(
            [Bound("recoverRapidity", Arrow(boundaryType, real))],
            new Formula.Not(ForAll(
                [Bound("eta", real)],
                Equal(Apply(recoverRapidity, BoundaryImage(eta)), eta))));
        Formula noObserverDecoder = ForAll(
            [Bound("recoverObserver", Arrow(boundaryType, observerStateType))],
            new Formula.Not(ForAll(
                [Bound("eta", real)],
                Equal(
                    Apply(recoverObserver, BoundaryImage(eta)),
                    ObserverState(eta)))));

        return Disp(Seq(
            Let(
                futurePoint,
                projectivePoint,
                Call("class", Call("pair", Varphi, D(1)))),
            Let(
                pastPoint,
                projectivePoint,
                Call("class", Call("pair", phiPrime, D(1)))),
            Let(observerOrbit, type, observerOrbitDefinition),
            Let(
                boundaryProjection,
                Arrow(observerOrbit, boundaryType),
                boundaryProjectionDefinition),
            Let(
                boundaryImage,
                Arrow(real, boundaryType),
                boundaryImageDefinition),
            All(
                fixedImage,
                distinctFibers,
                new Formula.Not(Call("Injective", boundaryProjection)),
                noRapidityDecoder,
                noObserverDecoder),
            Dot));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
