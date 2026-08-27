using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class TargetPredictionSufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Quantum/PredictionDepth/TargetPredictionSufficiency."
            + "target_prediction_sufficiency";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible targets are signature-determined; invisible targets separate physical states.",
        H("Target Prediction Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-prediction-sufficiency"),
                DeclarationHandle.Create(Gid),
                H("The visible span is exactly sufficient for target prediction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The visible real Hermitian subspace is constructed from the identity "
                            + "and the complete family of declared effects. If the target "
                            + "subspace lies inside it, equal physical-state signatures force "
                            + "equal expectations for every target observable.")),
                    Paragraph(Text(
                        "For an observable outside the visible span, subtract its orthogonal "
                            + "projection. The resulting nonzero residual is trace zero and has "
                            + "a nonzero trace pairing with the observable.")),
                    Paragraph(Text(
                        "Small symmetric perturbations of the maximally mixed state along that "
                            + "residual are density states. They agree on every current effect "
                            + "but have different expectation for the chosen observable."))),
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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula indexType = F.Id("Index");
        Formula index = F.Id("i");
        Formula effects = F.Id("E");
        Formula effectValue = F.Id("X");
        Formula targets = F.Id("T");
        Formula visible = F.Id("V");
        Formula observable = F.Id("A");
        Formula direction = F.Id("D");
        Formula eps = F.Id("eps");
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula rhoPlus = F.Id("rhoPlus");
        Formula rhoMinus = F.Id("rhoMinus");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula hermitian = Call("HermitianSpace", d);
        Formula matrix(Formula value) => Call("matrix", value);
        Formula effectAt = Apply(effects, index);
        Formula effectType = Seq(
            OpenBrace, Typed(effectValue, hermitian), Sp, Mid, Sp,
            Call("PosSemidef", matrix(effectValue)), Sp, Land, Sp,
            Call("PosSemidef", Seq(F.Id("I"), Sp, Minus, Sp, matrix(effectValue))),
            CloseBrace);
        Formula visibleDefinition = Call("span", reals, Call(
            "insert", Call("identityHermitian", d), Call("range", effects)));
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula expectation(Formula state, Formula target) =>
            Call("Tr", Seq(matrix(state), Sp, target));
        Formula readout(Formula state) => expectation(state, effectAt);
        Formula equalSignature(Formula left, Formula right) => Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            readout(left), Sp, Eq, Sp, readout(right));
        Formula forward = Seq(
            targets, Sp, Subseteq, Sp, visible, Sp, Rightarrow, Sp,
            Forall, Sp, Typed(observable, hermitian), Comma, Sp,
            observable, Sp, InMacro, Sp, targets, Comma, Sp,
            Typed(Seq(rho, Comma, Sp, sigma), stateType), Comma, Sp,
            Open, equalSignature(rho, sigma), Close, Sp, Rightarrow, Sp,
            expectation(rho, observable), Sp, Eq, Sp,
            expectation(sigma, observable));
        Formula inverseDimension = new Formula.Power(
            d, Grp(Seq(Minus, D(1))));
        Formula plusMatrix = Seq(
            inverseDimension, Sp, F.Id("I"), Sp, Plus, Sp,
            eps, Sp, direction);
        Formula minusMatrix = Seq(
            inverseDimension, Sp, F.Id("I"), Sp, Minus, Sp,
            eps, Sp, direction);
        Formula converse = Seq(
            Forall, Sp, Typed(observable, hermitian), Comma, Sp,
            Neg, Grp(Seq(observable, Sp, InMacro, Sp, visible)), Sp,
            Rightarrow, RowBreak, Grp(),
            Exists, Sp, Typed(direction, hermitian), Comma, Sp,
            Typed(eps, reals), Comma, Sp,
            Typed(Seq(rhoPlus, Comma, Sp, rhoMinus), stateType), Comma,
            RowBreak, Grp(),
            Call("Tr", direction), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            direction, Sp, InMacro, Sp,
            new Formula.Power(visible, Grp(Perp)), Sp, Land,
            RowBreak, Grp(),
            Call("Tr", Seq(direction, Sp, observable)), Sp, Neq, Sp, D(0),
            Sp, Land, Sp, D(0), Sp, Lt, Sp, eps, Sp, Land,
            RowBreak, Grp(),
            matrix(rhoPlus), Sp, Eq, Sp, plusMatrix, Sp, Land,
            RowBreak, Grp(),
            matrix(rhoMinus), Sp, Eq, Sp, minusMatrix, Sp, Land,
            RowBreak, Grp(),
            Open, equalSignature(rhoPlus, rhoMinus), Close, Sp, Land,
            RowBreak, Grp(),
            expectation(rhoPlus, observable), Sp, Neq, Sp,
            expectation(rhoMinus, observable));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, Sp,
            Typed(indexType, type), Comma, RowBreak, Grp(),
            Typed(effects, Arrow(indexType, effectType)), Comma, RowBreak, Grp(),
            Typed(targets, Call("Submodule", reals, hermitian)), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(visible, Call("Submodule", reals, hermitian)), Sp,
            Eq, Sp, visibleDefinition, SemiSpace,
            RowBreak, Grp(),
            OpenBracket, forward, CloseBracket, Sp, Land,
            RowBreak, Grp(),
            OpenBracket, converse, CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
