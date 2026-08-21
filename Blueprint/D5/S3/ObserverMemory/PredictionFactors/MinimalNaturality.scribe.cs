using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class MinimalNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal naturality forces the unique surjective predictive-completion factor.",
        H("Minimal Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-naturality-factor"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/MinimalNaturality."
                        + "minimal_naturality_factor"),
                H("Naturality forces commutation and the unique surjective completion factor"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau update a finite state carrier Y, q be its readout, and let a finite "
                            + "realization r map Y surjectively to W while preserving q through o. The "
                            + "source diagonal is evaluated by applying tau to each table diagonal; P_r "
                            + "and Q_r push tables and vectors through r.")),
                    Paragraph(Text(
                        "If Q_r Delta_tau equals Delta_sigma P_r for every nonempty address type and every "
                            + "evaluation table, the singleton address instance forces r tau = sigma r. The "
                            + "canonical predictive-completion universal property then supplies a surjective "
                            + "factor h to the completed-state carrier, and surjectivity of r makes h unique "
                            + "even after retaining only the two displayed factor clauses.")),
                    Paragraph(Text(
                        "Repository search found and directly applied the canonical declarations "
                            + "DeterministicCompletionMinimality.minimal_deterministic_completion and the "
                            + "CompletedState, completionProjection definitions. Pinned Mathlib search found "
                            + "Function.semiconj_iff_comp_eq and quotient-surjectivity ingredients; no single "
                            + "library theorem packaged this naturality converse. The loogle and leansearch "
                            + "executables were unavailable on PATH."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ObserverMemory/Refinement/PredictionCompletion")),
        ]));

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

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula Formula()
    {
        Formula yType = F.Id("Y");
        Formula oType = F.Id("O");
        Formula wType = F.Id("W");
        Formula addressType = F.Id("A");
        Formula tau = F.Id("tau");
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula o = F.Id("o");
        Formula sigma = F.Id("sigma");
        Formula table = F.Id("E");
        Formula factor = F.Id("h");
        Formula candidate = F.Id("hPrime");
        Formula finiteY = Seq(OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, yType, CloseBracket);
        Formula finiteW = Seq(OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, wType, CloseBracket);
        Formula nonemptyY = Seq(OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, yType, CloseBracket);
        Formula tableType = new Formula.TypeArrow(addressType,
            new Formula.TypeArrow(addressType, yType));
        Formula qType = new Formula.TypeArrow(yType, oType);
        Formula rType = new Formula.TypeArrow(yType, wType);
        Formula oMapType = new Formula.TypeArrow(wType, oType);
        Formula stateUpdateType = new Formula.TypeArrow(yType, yType);
        Formula sigmaType = new Formula.TypeArrow(wType, wType);
        Formula completed = Apply(F.Id("CompletedState"), tau, q);
        Formula projection = Apply(F.Id("completionProjection"), tau, q);
        Formula qPush = new Formula.Subscript(F.Id("Q"), r);
        Formula pPush = new Formula.Subscript(F.Id("P"), r);
        Formula deltaTau = new Formula.Subscript(Delta, tau);
        Formula deltaSigma = new Formula.Subscript(Delta, sigma);
        Formula naturality = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("A"),
            Seq(Operatorname, Grp(F.Id("Type"))),
            new Formula.Logic(
                Seq(Operatorname, Grp(F.Id("Nonempty")), Open, addressType, Close),
                FormulaLogicOperator.Implies,
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("E"),
                    tableType,
                    Equal(Apply(qPush, Apply(deltaTau, table)),
                        Apply(deltaSigma, Apply(pPush, table))))));
        Formula factorProperty(Formula h) => new Formula.Logic(
            Apply(F.Id("Surjective"), h),
            FormulaLogicOperator.And,
            Equal(projection, Compose(h, r)));
        Formula uniqueFactor = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("h"),
            new Formula.TypeArrow(wType, completed),
            new Formula.Logic(
                factorProperty(factor),
                FormulaLogicOperator.And,
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("hPrime"),
                    new Formula.TypeArrow(wType, completed),
                    new Formula.Logic(
                        factorProperty(candidate),
                        FormulaLogicOperator.Implies,
                        Equal(candidate, factor)))));

        return Disp(Seq(
            Forall, Sp, yType, Comma, Sp, oType, Comma, Sp, wType, Comma, Sp,
            finiteY, Comma, Sp, finiteW, Comma, Sp, nonemptyY, Comma, Esc,
            Typed(tau, stateUpdateType), Comma, Sp, Typed(q, qType), Comma, Sp,
            Typed(r, rType), Comma, Sp, Typed(o, oMapType), Comma, Sp,
            Typed(sigma, sigmaType), Comma, Esc,
            Apply(F.Id("Surjective"), r), Sp, Land, Sp,
            Equal(q, Compose(o, r)), Sp, Land, Sp,
            naturality, Sp, Rightarrow, Sp,
            Open, Equal(Compose(r, tau), Compose(sigma, r)),
            Close, Sp, Land, Sp, uniqueFactor, Dot));
    }
}
