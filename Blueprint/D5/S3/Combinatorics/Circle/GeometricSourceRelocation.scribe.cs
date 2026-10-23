using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class GeometricSourceRelocationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/GeometricSourceRelocation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive geometric source has an explicit physical-label permutation whose exact attained width is at most the half-modulus capacity.",
        H("Exact attained width for geometric circle sources"),
        Blocks(GeometricRelocation()), []));

    private static DocumentBlock GeometricRelocation()
    {
        Formula r = V("r"), m = V("m"), d = V("d"), n = V("n");
        Formula b = Pow(Num(2), m), k = Add(Mul(r, m), d);
        Formula t = Call("ediv", Sub(Pow(b, r), Num(1)), Sub(b, Num(1)));
        Formula a = Sub(d, Num(1)), A = Pow(Num(2), a);
        Formula C = Sub(Pow(Num(2), Sub(k, Num(1))), Num(1));
        Formula W = Sub(C, Call("min", Sub(A, Num(1)), Call("ediv", Sub(t, Num(1)), Num(2))));
        Formula labels = Call("finRange", k);
        Formula word = Call("append", Call("rotate", Call("take", Sub(k, Num(1)), labels), a),
            Call("drop", Sub(k, Num(1)), labels));
        Formula f = Call("actualSource", k, t);
        Formula height = Call("sum", Call("map", f, Call("take", n, word)));
        Formula conclusion = And(Call("Perm", word, labels), Le(W, C),
            Q(And(Le(Num(0), height), Le(height, W)), ("n", Nat())),
            Eq(Call("sum", Call("map", f, word)), Num(0)),
            Ex("n", Nat(), And(Le(n, k), Eq(height, W))));
        return Describe.Lean(DescribeId.Create("geometric-source-relocation"),
            DeclarationHandle.Create(Prefix + "geometric_source_relocation"),
            H("Exact width after relocating the low physical labels"),
            StatementSource.FromAuthor(Disp(Q(Imp(And(Le(Num(1), r), Le(Num(1), m), Le(Num(1), d)),
                conclusion), ("r", Nat()), ("m", Nat()), ("d", Nat())))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let r,m,d be arbitrary positive naturals, B=2^m, k=rm+d and t=(B^r-1)/(B-1), with the quotient taken in the naturals. Put a=d-1, A=2^a, C=2^(k-1)-1 and W=C-min(A-1,(t-1)/2), with integer subtraction and Euclidean division in the width. The literal word rotates the first k-1 entries of finRange(k) by a and appends its last entry. Thus its labels are a,...,k-2,0,...,a-1,k-1. It is a permutation of the original Fin(k) labels. Every natural-length prefix, including saturated takes beyond k, has integer sum in [0,W], the total is zero, W<=C, and some prefix of length at most k attains W. This includes r=1, m=1, d=1, their intersections and the empty low block.")),
                Paragraph(Text("Multiplication by two on residues modulo N=2^k-1 is a cyclic action because 2^k=1 modulo N. Each original label retains its position in that action even when values coincide. The unsigned representative U_i=s_i+N when the centered source s_i is negative, and U_i=s_i otherwise, is an integer potential: U_(i+1)-U_i=s_i, including the last-to-first edge. Contiguous physical sums therefore telescope in the integers; a modular relation alone would not control their heights.")),
                Paragraph(Text("The geometric quotient equals the r-term sum of powers of B. Write L_j=sum_(e<j) B^e and u_j=2At-(2A-1)L_j. The exact source identity 2^(jm+d)t=N L_j+u_j, together with representative range checks, gives the negative-label representatives at nu_j=a+jm for 1<=j<=r. The nonfinal returns satisfy At<=u_j<=2At, and all intervening powers of two remain in the same full physical envelope At<=U_i<=ABt for a<=i<=k-1. Its upper endpoint is attained at i=a+m; the last unsigned and centered representatives are (N+t)/2 and (t-N)/2. These bounds are derived from the source, with no annulus, unit, distinctness or true-period hypothesis.")),
                Paragraph(Text("The main block has heights U_(a+n)-At and attains M=ABt-At=C-(A-1) at n=m. Reinserting the low labels adds only nonnegative actual increments, ending at L=C-(t-1)/2 at n=k-1. The final physical label returns to zero. Both M and L are visited, so their maximum is exactly W. This is the attained width of the displayed word; no minimum over all permutations or global optimality is claimed.")),
                Paragraph(Text("The source reference is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This symbolic family construction is repository-derived and makes no literature-novelty claim. The earlier ThreeParentFamily sources form the sign-and-rotation subfamily r=3,m=2,d=R-2 for R>=4: modulo N, -2^(R-1)*21 equals 11*2^(R-1)-1. Their sources overlap; their schedules and optimality statements are not identified here. The full arbitrary-source Conjecture 3.1 remains open. No unit-cycle, girth or full-demand conclusion outside this source family is asserted."))),
            DescribeRole.Theorem);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Nat() => Name("Nat");
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] values)
    {
        Formula result = values[^1];
        for (var i = values.Length - 2; i >= 0; i--)
            result = new Formula.Logic(values[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
