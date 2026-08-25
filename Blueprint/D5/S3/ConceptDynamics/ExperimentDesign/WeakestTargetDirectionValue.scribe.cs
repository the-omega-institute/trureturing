using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class WeakestTargetDirectionValueDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/WeakestTargetDirectionValue."
            + "weakest_target_direction_experiment_value";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Experiment value improves the weakest target direction and maximizes finite "
            + "target-pair coverage, while trace-only gain can remain target-inert.",
        H("Weakest Target-Direction Experiment Value"),
        Blocks(Describe.Lean(
            DescribeId.Create("weakest-target-direction-experiment-value"),
            DeclarationHandle.Create(Declaration),
            H("Experiments should improve weakest target directions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "On a finite-dimensional real or complex inner-product space, the target "
                        + "projection is idempotent and symmetric, and both Gram operators are "
                        + "symmetric. A uniform positive Rayleigh gain on every nonzero target "
                        + "direction raises the infimum Rayleigh score strictly.")),
                Paragraph(Text(
                    "The displayed two-dimensional matrices give the contrast clause. The "
                        + "added operator raises trace in the second coordinate, but target "
                        + "compression to the first coordinate is unchanged and still merges "
                        + "states with distinct first coordinates.")),
                Paragraph(Text(
                    "For finite state and candidate types, experimentGain is the canonical set "
                        + "of current target defects removed by a candidate. Finite maximization "
                        + "constructs a candidate whose covered-pair cardinality is maximal."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Compose(params Formula[] maps)
    {
        var pieces = new List<Formula>();
        foreach (var map in maps)
        {
            if (pieces.Count > 0)
            {
                pieces.Add(Sp);
                pieces.Add(Circ);
                pieces.Add(Sp);
            }
            pieces.Add(map);
        }
        return Seq([.. pieces]);
    }

    private static Formula And(params Formula[] clauses)
    {
        var pieces = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (pieces.Count > 0)
            {
                pieces.Add(Sp);
                pieces.Add(Land);
                pieces.Add(Sp);
            }
            pieces.Add(clause);
        }
        return Seq([.. pieces]);
    }

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula vector = F.Id("V");
        Formula projection = F.Id("P");
        Formula baseline = F.Id("W");
        Formula added = new Formula.Subscript(F.Id("W"), F.Id("a"));
        Formula epsilon = Varepsilon;
        Formula direction = F.Id("x");
        Formula targetDirections = new Formula.SetBuilder(
            And(
                Seq(direction, Sp, Neq, Sp, D(0)),
                Seq(Call("P", direction), Sp, Eq, Sp, direction)),
            direction,
            vector);
        Formula projectedBaseline = Compose(projection, baseline, projection);
        Formula projectedAdded = Compose(projection, added, projection);
        Formula projectedCombined = Compose(
            projection, Seq(Open, baseline, Sp, Plus, Sp, added, Close), projection);
        Formula minimum(Formula op) => Call("iInfRayleigh", op, targetDirections);

        Formula spectralPremises = And(
            Call("RCLike", scalar),
            Call("NormedAddCommGroup", vector),
            Call("InnerProductSpace", scalar, vector),
            Call("FiniteDimensional", scalar, vector),
            Seq(Compose(projection, projection), Sp, Eq, Sp, projection),
            Call("IsSymmetric", projection),
            Call("IsSymmetric", baseline),
            Call("IsSymmetric", added),
            Call("Nonempty", targetDirections),
            Seq(
                Exists, Sp, epsilon, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                D(0), Sp, Lt, Sp, epsilon, Sp, Land, Sp,
                Forall, Sp, F.Id("x"), InMacro, targetDirections, Comma, Sp,
                epsilon, Sp, Leq, Sp, Call("Rayleigh", projectedAdded, F.Id("x"))));

        Formula spectralClause = Seq(
            Forall, Sp, scalar, Comma, Sp, vector, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            projection, Comma, Sp, baseline, Comma, Sp, added, Colon, Sp,
            Call("LinearEnd", scalar, vector), Comma, Sp,
            spectralPremises, Sp, Rightarrow, Sp,
            minimum(projectedBaseline), Sp, Lt, Sp, minimum(projectedCombined));

        Formula matrixP = Call("diag", D(1), D(0));
        Formula matrixAdded = Call("diag", D(0), D(1));
        Formula compressedBaseline = Compose(matrixP, D(0), matrixP);
        Formula compressedCombined = Compose(
            matrixP, Seq(Open, D(0), Sp, Plus, Sp, matrixAdded, Close), matrixP);
        Formula countermodelClause = And(
            Seq(Call("trace", D(0)), Sp, Lt, Sp,
                Call("trace", Seq(D(0), Sp, Plus, Sp, matrixAdded))),
            Seq(compressedBaseline, Sp, Eq, Sp, compressedCombined),
            Seq(
                Exists, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp,
                Arrow(Call("Fin", D(2)), Seq(Mathbb, Grp(F.Id("R")))), Comma, Sp,
                Call("x", D(0)), Sp, Neq, Sp, Call("y", D(0)), Sp, Land, Sp,
                Call("mulVec", compressedCombined, F.Id("x")), Sp, Eq, Sp,
                Call("mulVec", compressedCombined, F.Id("y"))));

        Formula state = F.Id("X");
        Formula currentType = F.Id("C");
        Formula response = F.Id("R");
        Formula targetType = F.Id("Y");
        Formula candidateType = F.Id("A");
        Formula current = F.Id("q");
        Formula experiment = F.Id("e");
        Formula target = F.Id("t");
        Formula candidate = F.Id("a");
        Formula best = F.Id("b");
        Formula gain(Formula selected) =>
            Call("ncard", Call("experimentGain", current,
                Call("e", selected), target));
        Formula discreteClause = Seq(
            Forall, Sp, state, Comma, Sp, currentType, Comma, Sp,
            response, Comma, Sp, targetType, Comma, Sp, candidateType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            current, Colon, Sp, Arrow(state, currentType), Comma, Sp,
            experiment, Colon, Sp, Arrow(candidateType, Arrow(state, response)), Comma, Sp,
            target, Colon, Sp, Arrow(state, targetType), Comma, Sp,
            And(Call("Fintype", state), Call("Fintype", candidateType),
                Call("Nonempty", candidateType)), Sp, Rightarrow, Sp,
            Exists, Sp, best, Colon, Sp, candidateType, Comma, Sp,
            Forall, Sp, candidate, Colon, Sp, candidateType, Comma, Sp,
            gain(candidate), Sp, Leq, Sp, gain(best));

        return Disp(new Formula.Aligned([
            Seq(OpenBracket, spectralClause, CloseBracket, Sp, Land),
            Seq(Grp(), OpenBracket, countermodelClause, CloseBracket, Sp, Land),
            Seq(Grp(), OpenBracket, discreteClause, CloseBracket, Dot),
        ]));
    }
}
