using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectFiniteObservationCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Born readouts admit normalized Borel responses with maximal global deviations.",
        H("Finite observations and global effect probabilities"),
        Blocks(
            Paragraph(Text(
                "Work in the complex matrices indexed by Fin d, with d at least one. "
                    + "An effect E satisfies positivity of E and of I minus E. "
                    + "A density is positive semidefinite with complex trace exactly one. "
                    + "The matrix space carries its usual finite product topology and Borel sigma algebra; "
                    + "I and zero denote the identity and zero matrices, and val forgets the effect subtype.")),
            Describe.Lean(
                DescribeId.Create("effect-finite-observation-countermodel"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Foundation/EffectFiniteObservationCountermodel."
                        + "finite_observation_countermodel"),
                H("Exact finite agreement with maximal global deviations"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix any finite set T of actual effects and any reference density. "
                            + "A positive a with three times a below one can be chosen so that every "
                            + "positive scalar effect tI with t at most three times a misses T. "
                            + "A finite induction uses one diagonal entry: a positive entry bounds a "
                            + "smaller gap, while a nonpositive entry cannot equal a positive scalar matrix.")),
                    Paragraph(Text(
                        "Set the response to one at 2aI and at aI divided by (n plus one) for every "
                            + "natural n, to zero at 3aI, and to the reference Born trace elsewhere. "
                            + "These exceptional points miss T, zero and I. The high set is countable, "
                            + "so the total response is Borel measurable. Trace positivity bounds the "
                            + "reference probabilities between zero and one on every effect.")),
                    Paragraph(Text(
                        "The distinct effects aI and 2aI sum to 3aI and attain binary defect two. "
                            + "The effect range bounds every admissible binary defect by two. Against "
                            + "any density, the scalar Born trace at aI divided by (n plus one) tends "
                            + "to zero while the response stays one. Thus every positive tolerance "
                            + "has a strict distance witness, and all effect distances are at most one.")),
                    Paragraph(Text(
                        "The response depends on T. Finite readouts can identify a density inside "
                            + "the globally additive Born model, while these responses need not satisfy "
                            + "that model's global additivity hypothesis. Exact and approximate global "
                            + "additivity representation theorems retain their hypotheses. No physical "
                            + "realization follows from this construction."))),
                DescribeRole.Theorem))));

    private static Formula P(Formula value) => Seq(Open, value, Close);

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

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));

    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[index]));
        }
        return Seq([.. items]);
    }

    private static Formula Imp(Formula premise, Formula result) =>
        Seq(P(premise), Sp, Implies, Sp, P(result));

    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula LeqTo(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Add(Formula left, Formula right) => P(Seq(left, Plus, right));
    private static Formula Sub(Formula left, Formula right) => P(Seq(left, Minus, right));
    private static Formula At(Formula function, Formula argument) => Seq(function, P(argument));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula Born(Formula density, Formula effect) =>
        Seq(Re, Sp, Call("Tr", Seq(density, Sp, effect)));

    private static Formula StatementFormula()
    {
        Formula d = F.Id("d"), t = F.Id("T"), p = F.Id("p");
        Formula e = F.Id("E"), f = F.Id("F"), x = F.Id("X");
        Formula rho = Rho, reference = Seq(Rho, Underscore, Grp(Star)), eta = F.Id("eta");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", Call("Fin", d), Call("Fin", d), complex);
        Formula identity = Seq(F.Id("I"), Underscore, Grp(d));
        Formula zero = Seq(D(0), Underscore, Grp(d));
        Formula Effect(Formula value) => And(Call("PosSemidef", value),
            Call("PosSemidef", Sub(identity, value)));
        Formula Density(Formula value) => And(Call("PosSemidef", value),
            Equal(Call("Tr", value), D(1)));
        Formula effectType = Seq(OpenBrace, x, Colon, Sp, matrix, Sp, Mid, Sp,
            Effect(x), CloseBrace);
        Formula Defect(Formula left, Formula right) =>
            Abs(Sub(Sub(At(p, Add(left, right)), At(p, left)), At(p, right)));
        Formula Admissible(Formula left, Formula right) =>
            And(Call("PosSemidef", left), Call("PosSemidef", right),
                Call("PosSemidef", Sub(identity, Add(left, right))));
        Formula Distance(Formula state, Formula value) => Abs(Sub(At(p, value), Born(state, value)));

        Formula range = All(e, matrix, Imp(Effect(e),
            And(LeqTo(D(0), At(p, e)), LeqTo(At(p, e), D(1)))));
        Formula matching = All(e, effectType,
            Imp(Seq(e, Sp, InMacro, Sp, t),
                Equal(At(p, Call("val", e)), Born(reference, Call("val", e)))));
        Formula defectBound = All(e, matrix, All(f, matrix,
            Imp(Admissible(e, f), LeqTo(Defect(e, f), D(2)))));
        Formula attained = Some(e, matrix, Some(f, matrix,
            And(Seq(e, Sp, Neq, Sp, f), Admissible(e, f), Equal(Defect(e, f), D(2)))));
        Formula distance = All(rho, matrix, Imp(Density(rho), And(
            All(e, matrix, Imp(Effect(e), LeqTo(Distance(rho, e), D(1)))),
            All(eta, real, Imp(Less(D(0), eta), Some(e, matrix,
                And(Effect(e), Less(Sub(D(1), eta), Distance(rho, e)))))))));

        return Disp(All(d, nat, Imp(LeqTo(D(1), d),
            All(t, Call("Finset", effectType), All(reference, matrix,
                Imp(Density(reference), Some(p, Seq(matrix, Sp, To, Sp, real), And(
                    Call("Measurable", p), range,
                    Equal(At(p, zero), D(0)), Equal(At(p, identity), D(1)),
                    matching, defectBound, attained, distance))))))));
    }
}
