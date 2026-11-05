using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ExpandingSourcePathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula k = V("k"), t = V("t"), p = V("p"), m = V("m"), j = V("j"),
            n = V("n"), negative = V("negative");
        Formula source = Call("actualSource", k, t), N = Call("modulus", k);
        Formula x = Call("phase", p, m), P = Call("path", p, m);
        Formula s0 = Call("actualSource", k, t, p), sx = Call("actualSource", k, t, x);
        Formula d = Sub(Mul(Num(3), Call("orient", negative, s0)), N);
        Formula fj = Call("phase", p, j);
        Formula prefix = Call("orient", negative,
            Call("sum", Call("map", source, Call("take", n, P))));
        Formula r = Call("orient", negative, sx);
        Formula gap = Sub(Call("abs", sx),
            Call("abs", Call("actualSource", k, t, Call("phase", p, Sub(m, Num(2))))));
        Formula assumptions = And(Le(Num(3), k), Le(Num(2), m),
            Eq(Call("mod", m, Num(2)), Num(0)), Lt(Num(0), d),
            Q(Imp(Lt(j, m), Call("Large", k, t, fj)), ("j", Name("Nat"))));
        Formula conclusion = And(Lt(Num(0), r), Call("Large", k, t, x),
            Q(And(Le(Num(0), prefix), Le(prefix, r)), ("n", Name("Nat"))),
            Eq(gap, Mul(Pow(Num(2), Sub(m, Num(2))), d)),
            Le(Sub(Call("intCast", m), Num(1)), gap),
            Lt(Call("sum", Call("map", Call("sourcePowerEnergy", k, t), P)),
                Pow(Num(3), Call("natAbs", sx))));
        Formula statement = Q(Imp(assumptions, conclusion),
            ("k", Name("Nat")), ("t", Name("Nat")), ("p", Call("Fin", k)),
            ("m", Name("Nat")), ("negative", Name("Bool")));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual source paths: actual even expanding paths force every oriented prefix into [0,r] and their physical energy below the consumed endpoint's energy.",
            H("Even expanding paths in the original centered source"),
            Blocks(
                Describe.Lean(DescribeId.Create("native-even-expanding-path-estimates"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ExpandingSourcePath.expanding_path_estimates"),
                    H("Source-forced prefix and exponential estimates"),
                    StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("The source is exactly SourceWidth.actualSource(k,t,p) = centered(2^k-1,2^p*t), with physical p in Fin(k). Q=2^(k-2), N=4Q-1, C=N/2=2Q-1, k>=3. LARGE means Q<=|s(p)|. phase(p,j) has value (p.val+j) mod k, and path(p,m) is its first m physical occurrences. The omitted proof argument of phase/path is only 0<k. sourcePowerEnergy in the displayed formula abbreviates the lambda q => 3^(natAbs(actualSource k t q)); it is notation here, not an added Lean definition.")),
                        Paragraph(Text("The orientation flag changes signs of values only. Its premise d=3*orient(s(p))-N>0 forces a positive oriented start. The LARGE and centered-bound hypotheses of the private recurrence lemma are discharged by the native source, rather than passed through as an uninstantiated scalar model. phase_step uses SourceWidth.centered_double for ordinary edges and centered_full_period for the physical seam.")),
                        Paragraph(Text("The recurrence induction derives both sign alternation and 3*w_j = (N for even j, -N for odd j) + 2^j*d. A second induction derives 3*F_j = (0 for even j, N for odd j) + (2^j-1)*d. Since d is a positive integer and j<=m with m even, these imply 0<=F_j<=r=w_m. Taking min(n,m) proves the bound for every natural take, including empty and overlength takes.")),
                        Paragraph(Text("The largest inserted magnitude is M=|w_(m-2)|: even-indexed magnitudes increase, and each odd-indexed magnitude is below N/3. The exact integer gap r-M=2^(m-2)*d is proved from the two native even-index equations. Induction gives 2^(m-2)>=m-1 and 3^(m-1)>m, hence sum_(j<m)3^|s(a_j)| <= m*3^M < 3^r. The desired energy drop is a conclusion, never a premise.")),
                        Paragraph(Text("This module supplies the analytic estimates consumed by MixedSuffixEnergy.mixed_suffix_energy_exchange. The physical unusedness, distinctness, prefix A, and inventory argument belong to that consumer. No unit, primitivity, distinct-value, or full numerical-period assumption occurs. This path theorem does not cover d=0 or k<3, and does not assert that an eligible path exists in an arbitrary incomplete word."))),
                    DescribeRole.Theorem)), []));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Name(string s) => new Formula.NamedConstant(FormulaIdentifier.Create(s));
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] vs)
    {
        for (var i = vs.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(vs[i].Name), vs[i].Domain, body);
        return body;
    }
    private static Formula And(params Formula[] a)
    {
        var body = a[^1];
        for (var i = a.Length - 2; i >= 0; --i) body = new Formula.Logic(a[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
