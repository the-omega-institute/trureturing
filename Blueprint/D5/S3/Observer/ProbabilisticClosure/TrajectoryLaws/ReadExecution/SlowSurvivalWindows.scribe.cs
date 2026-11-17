using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class SlowSurvivalWindowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered waiting windows from slow survival decay", H("Ordered waiting windows from slow survival decay"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-waiting-windows"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/SlowSurvivalWindows.finite_waiting_windows"),
                H("Jointly ordered finite windows"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive real sequence S tending to zero whose successive ratios tend to one, every natural K and every positive real theta admit the displayed finite witnesses. The single strictly increasing boundary vector b encodes L(i)=b(i.castSucc), U(i)=b(i.succ) and H=b(last K). Thus the first lower endpoint is zero, successive windows meet exactly, and every upper endpoint is at most the same H. The selected positive ages n(i) are strictly increasing. When K is zero, the age family is empty, the boundary vector has its single zero entry and H is zero; otherwise H and every window length are positive.")),
                    Paragraph(Text("At each fixed length L, the quotient S(n+L)/S(n) tends to one by multiplying the L successive ratios; the empty product is one. At fixed n, S(n+U)/S(n) tends to zero because S(n) is positive. A recursive witness construction first chooses an age larger than the previous age with early ratio greater than 1-theta, then an upper endpoint beyond the previous boundary with tail ratio less than theta. Subtracting these inequalities gives the strict bound 1-2*theta. No rate, uniform limit or monotonicity of S is used. Positivity of theta suffices, so the theorem also applies in the source range theta less than 1/16.")),
                    Paragraph(Text("The conclusion concerns an arbitrary positive scalar sequence with the two stated limits. Applying it to a diffusion survival sequence requires proving those hypotheses for that diffusion; cylinder probabilities, stationary laws and full-history conditional distributions are additional data. The scalar inequalities alone do not assert a diffusion realization or a bound on a finite bank of predictive distributions."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula LambdaFormula(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Par(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, Par(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula premise, Formula result) => Seq(Par(premise), Sp, Rightarrow, Sp, result);
    private static Formula Both(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = Seq(Par(clauses[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula Lower => Call("b", Call("castSucc", V("i")));
    private static Formula Upper => Call("b", Call("succ", V("i")));
    private static Formula Age => Call("n", V("i"));
    private static Formula Bound => Subtract(D(1), Multiply(D(2), V("theta")));
    private static Formula Conclusion()
    {
        var mass = new Formula.Fraction(
            Subtract(Call("S", Add(Age, Lower)), Call("S", Add(Age, Upper))), Call("S", Age));
        var rows = All("i", Call("Fin", V("K")),
            Both(Lt(D(0), Age), Lt(Lower, Upper), Le(Upper, V("H")), Lt(Bound, mass)));
        var result = Both(Eqn(Call("b", D(0)), D(0)), Eqn(Call("b", Call("last", V("K"))), V("H")),
            Seq(Par(Eqn(V("K"), D(0))), Sp, Iff, Sp, Par(Eqn(V("H"), D(0)))),
            Call("StrictMono", V("b")), Call("StrictMono", V("n")), rows);
        result = Some("b", new Formula.TypeArrow(Call("Fin", Add(V("K"), D(1))), Nat), result);
        result = Some("n", new Formula.TypeArrow(Call("Fin", V("K")), Nat), result);
        return Some("H", Nat, result);
    }
    private static Formula Statement()
    {
        var result = All("K", Nat, All("theta", Real, Imp(Lt(D(0), V("theta")), Conclusion())));
        var ratio = LambdaFormula("j", Nat,
            new Formula.Fraction(Call("S", Add(V("j"), D(1))), Call("S", V("j"))));
        result = Imp(Call("Tendsto", ratio, V("atTop"), Call("nhds", D(1))), result);
        result = Imp(Call("Tendsto", V("S"), V("atTop"), Call("nhds", D(0))), result);
        result = Imp(All("j", Nat, Lt(D(0), Call("S", V("j")))), result);
        return All("S", new Formula.TypeArrow(Nat, Real), result);
    }
}
