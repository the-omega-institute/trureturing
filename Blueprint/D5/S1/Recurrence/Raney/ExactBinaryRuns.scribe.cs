using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class ExactBinaryRunsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Raney sequence R(3,1) modulo two has exactly the positive maximal zero-run lengths floor(2^m/3), with explicit earliest record intervals.",
        H("Exact Binary Raney Zero Runs"),
        Blocks(
            Paragraph(Text(
                "The binary clause of Ma and Zhang's Complete small-prime record spectra for R(3,1): proofs "
                    + "concerns the literal natural quotient raneyNumber(3,1,n), reduced modulo two only after "
                    + "the integral division. Write rho(n) for this residue and Z(a,b) for "
                    + "IsMaximalDeltaInterval({0},rho,a,b). Thus a<=b, every index in [a,b] has residue zero, "
                    + "the right neighbor has nonzero residue, and either a=0 or the left neighbor has nonzero residue. "
                    + "Here rho(0)=1, so the a=0 alternative cannot occur.")),
            Paragraph(Text(
                "For natural m, let L(m)=floor(2^m/3) and A(m)=ceil(2^(m+1)/3)=(2^(m+1)+2)/3, "
                    + "with natural division. The theorem quantifies over every finite nonempty maximal interval "
                    + "at every natural index. A record uses the source's weak comparison with earlier runs, "
                    + "allowing ties; the displayed earliest occurrence satisfies the stronger strict comparison.")),
            Describe.Lean(
                DescribeId.Create("raney-binary-exact-zero-run-spectrum"),
                DeclarationHandle.Create("D5/S1/Recurrence/Raney/ExactBinaryRuns.raney_binary_exact_zero_run_spectrum"),
                H("Complete Binary Spectrum and Earliest Records"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every actual maximal zero interval [a,b] has length L(m) for some m>=2 and a>=A(m). "
                            + "Conversely, [A(m),2^m-1] is an actual maximal zero interval of length L(m) for every m>=2. "
                            + "Every maximal interval beginning before A(m) has strictly smaller length. Finally, "
                            + "L(m)<L(k) whenever 2<=m<k. These statements give equality of the positive maximal-run "
                            + "spectrum and the distinct positive record spectrum, with no repeated retained lengths.")),
                    Paragraph(Text(
                        "The proof establishes the integral adjacent-binomial identity before taking residues. "
                            + "Lucas's theorem then gives support at 2n exactly when there is support at n, support "
                            + "at 4n+1 exactly when there is support at n, and no support at 4n+3. These are identities "
                            + "about the literal Raney sequence; no mask or correctness assumption is supplied.")),
                    Paragraph(Text(
                        "The top half of each binary prefix has the support of a translated shorter prefix. "
                            + "Its greatest supported index is floor(2^(m+1)/3). A positive gap between consecutive "
                            + "supported indices either descends to a shorter prefix, translates to one, or is the "
                            + "terminal gap. The descent covers every finite gap and tracks the right endpoint "
                            + "2^m as a lower bound, which supplies the first-occurrence bound. The terminal gap "
                            + "has both actual nonzero neighbors. This document asserts only the binary clause; "
                            + "the ternary and larger-prime clauses require their own proofs."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula And(params Formula[] xs)
    {
        Formula result = xs[0];
        for (var i = 1; i < xs.Length; i++) result = new Formula.Logic(result, FormulaLogicOperator.And, xs[i]);
        return result;
    }
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), N(), body);
    private static Formula Ex(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), N(), body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula L(Formula m) => Call("NatDiv", Pow(D(2), m), D(3));
    private static Formula A(Formula m) => Call("NatDiv", Add(Pow(D(2), Add(m, D(1))), D(2)), D(3));
    private static Formula Len(Formula a, Formula b) => Sub(Add(b, D(1)), a);
    private static Formula Z(Formula a, Formula b) => Call("Z", a, b);

    private static Formula ResultFormula()
    {
        var m = V("m");
        var k = V("k");
        var a = V("a");
        var b = V("b");
        var end = Sub(Pow(D(2), m), D(1));
        var complete = All("a", All("b", Implies(Z(a, b), Ex("m",
            And(LeF(D(2), m), Eqn(Len(a, b), L(m)), LeF(A(m), a))))));
        var earlier = All("a", All("b", Implies(And(Z(a, b), LtF(a, A(m))),
            LtF(Len(a, b), L(m)))));
        var witnesses = All("m", Implies(LeF(D(2), m),
            And(Z(A(m), end), Eqn(Len(A(m), end), L(m)), earlier)));
        var increasing = All("m", All("k", Implies(And(LeF(D(2), m), LtF(m, k)),
            LtF(L(m), L(k)))));
        return Disp(And(Paren(complete), Paren(witnesses), Paren(increasing)));
    }
}
