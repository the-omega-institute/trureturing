using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FiniteShiftedRecordChannelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete finite shifted records realize the normalized coefficient coherence channel.",
        H("Finite Shifted Record Realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shifted-coefficient-records"),
                DeclarationHandle.Create(Owner + "shifted_coefficient_records"),
                H("Concrete normalized records and their signed overlaps"),
                StatementSource.FromAuthor(TheoremFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "S is an arbitrary finite system basis. Integer labels q may repeat or be "
                    + "negative, and S may be empty. The coefficient function is zero outside "
                    + "the integer interval from zero to N and its squared norms sum to one. "
                    + "Q is the sum of absolute labels, so the explicit interval D contains every "
                    + "shifted support. Its coordinate enumeration is both onto D and injective. "
                    + "The record norms and overlaps follow from the coefficient hypotheses by "
                    + "finite reindexing; they are conclusions, not additional hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-kraus-complete"),
                DeclarationHandle.Create(Owner + "diagonal_kraus_complete"),
                H("Finite unit-norm records give a complete diagonal Kraus family"),
                StatementSource.FromAuthor(DiagonalKrausFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite index types ι and ε, any complex record whose rows have squared "
                    + "norm one yields diagonal Kraus operators whose adjoint products sum to "
                    + "the identity matrix. The theorem is uniform in both finite carriers and "
                    + "the record values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-shifted-record-channel"),
                DeclarationHandle.Create(Owner + "finite_shifted_record_channel"),
                H("The actual finite marginal is a completely positive trace-preserving channel"),
                StatementSource.FromAuthor(TheoremFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The actual recording V sends basis vector i to i tensored with E(i). "
                        + "T sums equal environment coordinates and Lambda is defined by applying "
                        + "T to V rho V adjoint. The channel is never defined by the desired entry "
                        + "formula. The frozen environment marginal theorem supplies that formula "
                        + "after finite-coordinate transport and substitution of the proved overlap.")),
                    Paragraph(Text(
                        "QuantumChannel is the canonical FiniteStateChannel bundle of Mathlib "
                        + "CompletelyPositiveMap on CStarMatrix and trace preservation. Its "
                        + "positivity holds at every finite amplification, and both its equality "
                        + "with Lambda and the entry identity hold for every complex matrix. "
                        + "toCstar and fromCstar denote CStarMatrix.ofMatrix and its inverse; "
                        + "adjoint means conjugate transpose. The integer gamma sum is the tsum "
                        + "of the zero-extended coefficients.")),
                    Paragraph(Text(
                        "This is one finite isometric realization. It makes no claim of energy "
                        + "conservation for a specified Hamiltonian, spatial locality, zero operation "
                        + "cost, or universality over all reference devices. QUANTUM-REALITY "
                        + "definition74.1 and theorem74.1 supply the source provenance; commentary "
                        + "there about existing repository code is not an extra mathematical claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(params string[] parts) => Seq(parts.SelectMany(
        (part, index) => index == 0
            ? new[] { F.Id(part) }
            : new[] { Dot, F.Id(part) }).ToArray());
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Bin(Formula a, FormulaBinaryOperator op, Formula b) =>
        new Formula.Binary(a, op, b);
    private static Formula Add(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(a, op, b);
    private static Formula Both(params Formula[] terms) => terms.Aggregate(
        (a, b) => Logic(a, FormulaLogicOperator.And, b));
    private static Formula Adjoint(Formula a) => Seq(a, Caret, Grp(Star));
    private static Formula SumOver(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, domain), Sp, Grp(body));
    private static Formula Let(Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, body, Semi, Sp);

    private static Formula LambdaTyped(string name, Formula type, Formula body) =>
        Seq(Open, F.Id("fun"), Sp, Seq(Open, F.Id(name), Colon, type, Close), Sp,
            Mapsto, Sp, body, Close);

    private static Formula SumOverType(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Sp, body);

    private static Formula DiagonalKrausFormula()
    {
        Formula system = F.Id("I"), environment = F.Id("E");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula recordType = new Formula.TypeArrow(system,
            new Formula.TypeArrow(environment, complex));
        Formula record = F.Id("record"), i = F.Id("i"), a = F.Id("a");
        Formula rowValue = Apply(Apply(record, i), a);
        Formula rowNorm = SumOverType("a", environment,
            Seq(Call("norm", rowValue), Caret, Grp(Num(2))));
        Formula rowHypothesis = All([Bound("i", system)], Eqn(rowNorm, Num(1)));
        Formula diagonal = new Formula.Apply(Qualified("Matrix", "diagonal"),
            [LambdaTyped("i", system, rowValue)]);
        Formula conclusion = Eqn(
            SumOverType("a", environment, Seq(Adjoint(diagonal), Sp, Cdot, Sp, diagonal)),
            Num(1));
        Formula statement = All([Bound("record", recordType)],
            Logic(rowHypothesis, FormulaLogicOperator.Implies, conclusion));
        statement = Seq(OpenBracket, Call("Fintype", environment), CloseBracket, Sp,
            statement);
        statement = All([Bound("E", F.Id("Type"))], statement);
        statement = Seq(OpenBracket, Call("Fintype", system), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", system), CloseBracket, Sp, statement);
        statement = All([Bound("I", F.Id("Type"))], statement);
        return Disp(statement);
    }

    private static Formula TheoremFormula(bool realization)
    {
        Formula system = F.Id("S"), nmax = F.Id("N"), c = F.Id("c"), q = F.Id("q");
        Formula radius = F.Id("Q"), length = F.Id("L"), interval = F.Id("D");
        Formula coord = F.Id("coord"), record = F.Id("E"), gamma = GammaLower;
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("a"), m = F.Id("m"), n = F.Id("n");
        Formula ell = F.Id("ell"), v = F.Id("V"), trace = F.Id("T"), joint = F.Id("X");
        Formula channel = F.Id("C"), rho = F.Id("rho");
        Formula integer = Seq(Mathbb, Grp(F.Id("Z"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula support = Call("Icc", Num(0), nmax), env = Call("Fin", length);
        Formula input = Call("Matrix", system, system, complex);
        Formula product = Seq(system, Sp, Times, Sp, env);
        Formula output = Call("Matrix", product, product, complex);
        Formula Rec(Formula x, Formula y) => Apply(Apply(record, x), y);
        Formula NormSq(Formula x) => Seq(Call("norm", x), Caret, Grp(Num(2)));
        Formula Entry(Formula x, Formula y, Formula z) => Call("entry", x, y, z);
        Formula ci = Apply(c, n), qi = Apply(q, i), qj = Apply(q, j);
        Formula coefficientTerm = Mul(Apply(c, Add(n, ell)), Call("conj", ci));
        Formula hypotheses = Both(
            All([Bound("n", integer)], Logic(
                Logic(Rel(n, FormulaRelationOperator.LessThan, Num(0)), FormulaLogicOperator.Or,
                    Rel(nmax, FormulaRelationOperator.LessThan, n)),
                FormulaLogicOperator.Implies, Eqn(ci, Num(0)))),
            Eqn(SumOver(n, support, NormSq(ci)), Num(1)));
        Formula definitions = Seq(
            Let(Eqn(radius, SumOver(i, system, Call("natAbs", qi)))),
            Let(Eqn(length, Add(Add(nmax, Mul(Num(2), radius)), Num(1)))),
            Let(Eqn(interval, Call("Icc", Seq(Minus, radius), Add(nmax, radius)))),
            Let(All([Bound("a", env)], Eqn(Apply(coord, a), Sub(Call("int", a), radius)))),
            Let(All([Bound("i", system), Bound("a", env)],
                Eqn(Rec(i, a), Apply(c, Add(Apply(coord, a), qi))))),
            Let(All([Bound("ell", integer)], Eqn(Apply(gamma, ell),
                SumOver(n, support, coefficientTerm)))));
        Formula recordClauses = Both(
            Eqn(Call("range", coord), interval), Call("Injective", coord),
            All([Bound("i", system), Bound("m", integer)], Logic(
                Rel(Apply(c, Add(m, qi)), FormulaRelationOperator.NotEqual, Num(0)),
                FormulaLogicOperator.Implies, Rel(m, FormulaRelationOperator.MemberOf, interval))),
            All([Bound("i", system)], Eqn(SumOver(a, env, NormSq(Rec(i, a))), Num(1))),
            All([Bound("i", system), Bound("j", system)], Eqn(
                SumOver(a, env, Mul(Call("conj", Rec(j, a)), Rec(i, a))),
                Apply(gamma, Sub(qi, qj)))));
        Formula conclusion = recordClauses;
        if (realization)
        {
            Formula lambda = Lambda, pairIA = Call("pair", i, a), pairJA = Call("pair", j, a);
            definitions = Seq(definitions,
                Let(All([Bound("i", system), Bound("a", env), Bound("j", system)],
                    Eqn(Entry(v, pairIA, j), Call("ite", Eqn(j, i), Rec(i, a), Num(0))))),
                Let(All([Bound("X", output), Bound("i", system), Bound("j", system)],
                    Eqn(Entry(Apply(trace, joint), i, j), SumOver(a, env, Entry(joint, pairIA, pairJA))))),
                Let(All([Bound("rho", input)], Eqn(Apply(lambda, rho),
                    Apply(trace, Mul(Mul(v, rho), Adjoint(v)))))));
            Formula bundled = new Formula.BindMany(FormulaQuantifier.Exists,
                [Bound("C", Call("QuantumChannel", system, system))],
                All([Bound("rho", input)], Eqn(
                    Call("fromCstar", Call("apply", channel, Call("toCstar", rho))),
                    Apply(lambda, rho))));
            conclusion = Both(recordClauses,
                All([Bound("ell", integer)], Eqn(Apply(gamma, ell),
                    SumOver(n, integer, coefficientTerm))),
                Eqn(Mul(Adjoint(v), v), Num(1)), bundled,
                All([Bound("rho", input), Bound("i", system), Bound("j", system)],
                    Eqn(Entry(Apply(lambda, rho), i, j),
                        Mul(Apply(gamma, Sub(qi, qj)), Entry(rho, i, j)))),
                All([Bound("rho", input)], Eqn(Call("trace", Apply(lambda, rho)),
                    Call("trace", rho))));
        }
        return Disp(All(
            [Bound("S", F.Id("FiniteType")), Bound("N", F.Id("Nat")),
                Bound("c", new Formula.TypeArrow(integer, complex)),
                Bound("q", new Formula.TypeArrow(system, integer))],
            Logic(hypotheses, FormulaLogicOperator.Implies, Seq(definitions, conclusion))));
    }
}
