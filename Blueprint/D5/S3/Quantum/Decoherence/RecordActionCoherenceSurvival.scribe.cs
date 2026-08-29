using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class RecordActionCoherenceSurvivalDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Decoherence/RecordActionCoherenceSurvival."
            + "record_action_controls_coherence_survival";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized record overlaps control coherence survival and its logarithmic rate.",
        H("Record Action Controls Coherence Survival"),
        Blocks(Describe.Lean(
            DescribeId.Create("record-action-controls-coherence-survival"),
            DeclarationHandle.Create(Declaration),
            H("Record action controls coherence survival"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Each record overlap is constructed from the Hilbert inner product of the "
                    + "normalized record vectors. Their finite product defines the surviving "
                    + "coherence, and its extended negative logarithm defines the record action."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), address = F.Id("I"), environment = F.Id("E");
        Formula record = F.Id("R"), i = F.Id("i"), j = F.Id("j");
        Formula initial = F.Id("rho0"), n = F.Id("N");
        Formula r = F.Id("r"), lambda = F.Id("lambda");
        Formula nat = Seq(Mathbb, Grp(F.Id("N"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula extended = Seq(OpenBracket, D(0), Comma, Sp, Infty, CloseBracket);
        Formula overlap = F.Id("g"), cumulativeFunction = F.Id("Gamma");
        Formula actionFunction = F.Id("A"), rhoFunction = F.Id("rho");
        Formula cumulative = Apply(cumulativeFunction, n);
        Formula action = Apply(actionFunction, n), rhoN = Apply(rhoFunction, n);
        Formula recordAt = Apply(record, r, i);
        Formula recordType = Arrow(nat, Arrow(address, environment));
        Formula normalized = BindMany([Bound("r", nat), Bound("i", address)],
            Equal(new Formula.Norm(recordAt), D(1)));
        Formula overlapDefinition = Seq(Operatorname, Grp(F.Id("let")), Sp,
            overlap, Colon, Sp, Arrow(nat, complex), Sp, Eq, Sp,
            r, Colon, Sp, nat, Sp, Mapsto, Sp,
            Call("inner", Apply(record, r, j), recordAt), Semi);
        Formula cumulativeDefinition = Seq(Operatorname, Grp(F.Id("let")), Sp,
            cumulativeFunction, Colon, Sp, Arrow(nat, complex), Sp, Eq, Sp,
            n, Colon, Sp, nat, Sp, Mapsto, Sp, Call("rangeProduct", n, overlap), Semi);
        Formula actionDefinition = Seq(Operatorname, Grp(F.Id("let")), Sp,
            actionFunction, Colon, Sp, Arrow(nat, extended), Sp, Eq, Sp,
            n, Colon, Sp, nat, Sp, Mapsto, Sp,
            Call("toENNReal", Call("negLog", Call("ofReal", new Formula.Norm(cumulative)))), Semi);
        Formula rhoDefinition = Seq(Operatorname, Grp(F.Id("let")), Sp,
            rhoFunction, Colon, Sp, Arrow(nat, complex), Sp, Eq, Sp,
            n, Colon, Sp, nat, Sp, Mapsto, Sp, Multiply(cumulative, initial), Semi);
        Formula survival = BindMany([Bound("N", nat)], Equal(
            Call("ofReal", new Formula.Norm(rhoN)),
            Multiply(Call("exp", new Formula.Negate(Call("coeEReal", action))),
                Call("ofReal", new Formula.Norm(initial)))));
        Formula monotone = Call("Monotone", actionFunction);
        Formula actionRate = Call("TendstoAtTop", n, nat,
            new Formula.Fraction(Call("coeEReal", action), Call("coeEReal", n)), lambda);
        Formula erasureRate = Call("TendstoAtTop", n, nat,
            new Formula.Fraction(
                Call("negLog", new Formula.Fraction(
                    Call("ofReal", new Formula.Norm(rhoN)),
                    Call("ofReal", new Formula.Norm(initial)))),
                Call("coeEReal", n)), lambda);
        Formula rateClause = BindMany([Bound("lambda", F.Id("EReal"))],
            Implies(actionRate, erasureRate));
        Formula conclusion = Seq(overlapDefinition, cumulativeDefinition, actionDefinition,
            rhoDefinition, And(survival, And(monotone, rateClause)));
        Formula instances = And(Call("NormedAddCommGroup", environment),
            Call("InnerProductSpace", complex, environment));
        Formula nonzero = new Formula.Relation(initial, FormulaRelationOperator.NotEqual, D(0));
        Formula assumptions = And(instances, And(normalized, nonzero));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("I", type), Bound("E", type), Bound("R", recordType),
                Bound("i", address), Bound("j", address), Bound("rho0", complex)],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula BindMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
