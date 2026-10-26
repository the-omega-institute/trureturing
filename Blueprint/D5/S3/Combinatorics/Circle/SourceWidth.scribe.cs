using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class SourceWidthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/SourceWidth.";

    public DocumentDefinition Create()
    {
        Formula k = V("k"), t = V("t"), p = V("p"), n = V("n"), w = V("word");
        Formula N = Call("modulus", k), B = Call("capacity", k);
        Formula source = Call("actualSource", k, t);
        Formula height = Call("sum", Call("map", source, Call("take", n, w)));
        Formula complete = And(Call("Nodup", w), Eq(Call("toFinset", w), Name("univ")),
            Q(Imp(Le(n, k), And(Le(Num(0), height), Le(height, B))), ("n", Nat())));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every centered doubling source of length k at least three has one complete physical-label permutation whose every prefix lies between zero and N minus floor(N/3) minus two.",
            H("A universal support width for centered circle sources"),
            Blocks(
                Node("modulus", "The original odd modulus", "modulus",
                    Disp(Q(Eq(N, Sub(Pow(Num(2), k), Num(1))), ("k", Nat()))),
                    "The integer modulus is N = 2^k - 1. The width theorem assumes k at least three, so N is at least seven.",
                    DescribeRole.Definition),
                Node("centered", "Centered residues", "centered",
                    Disp(Q(Eq(Call("centered", V("N"), V("x")),
                        Sub(Call("emod", Add(V("x"), Call("ediv", V("N"), Num(2))), V("N")),
                            Call("ediv", V("N"), Num(2)))), ("N", Int()), ("x", Int()))),
                    "Division and remainder are integer Euclidean operations. For positive odd N this selects the unique congruent integer in [-floor(N/2), floor(N/2)].",
                    DescribeRole.Definition),
                Node("source", "All physical source occurrences", "actualSource",
                    Disp(Q(Eq(Call("actualSource", k, t, p),
                        Call("centered", N, Mul(Pow(Num(2), Call("val", p)), t))),
                        ("k", Nat()), ("t", Nat()), ("p", Call("Fin", k)))),
                    "The position p in Fin(k) is the physical label. Equal values at different positions remain different occurrences. The natural parameter t is unrestricted; reduction modulo N includes zero, nonunits and sources whose least period is smaller than k.",
                    DescribeRole.Definition),
                Node("capacity", "The support capacity", "capacity",
                    Disp(Q(Eq(B, Sub(Sub(N, Call("ediv", N, Num(3))), Num(2))), ("k", Nat()))),
                    "Writing A = floor(N/3), the capacity is B = N - A - 2. For k at least three, A is at least two and N is either 3A or 3A+1.",
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("universal-source-width"),
                    DeclarationHandle.Create(Prefix + "universal_source_width"),
                    H("One complete word with every height in the support strip"),
                    StatementSource.FromAuthor(Disp(Q(Imp(Le(Num(3), k),
                        Ex("word", Call("List", Call("Fin", k)), complete)), ("k", Nat()), ("t", Nat())))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every k at least three and every natural t, there is one list word of distinct Fin(k) labels containing all labels. For each n from zero through k, the sum of its first n actual source values is in the closed integer interval [0,B]. The interval membership in Lean is exactly the conjunction of the two displayed inequalities. No zero-sum, packet partition, compatible boundary vector or generic source property is assumed by this theorem.")),
                        Paragraph(Text("The centered arithmetic gives the strict source successor: 2s when 4|s| < N, 2s-N when 4s > N, and 2s+N when 4s < -N. Odd N excludes both half endpoints. With epsilon equal to one for negative s and zero otherwise, u = s + N epsilon satisfies u_next-u = s. The code retains this potential identity and the original successor in SourcePath. The congruence 2^k = 1 modulo N closes the path on the original k physical labels. Telescoping gives the original cyclic sum zero; no successor relation is applied to contracted nets.")),
                        Paragraph(Text("A large label has |s| > A. Its immediate successor has the opposite sign and magnitude b = N-2|s| in [1,A]. Between this parent and the next large label, two consecutive small values must be related by doubling. The only exception could be N=3A and a value equal to A or -A. That exceptional orbit remains trapped in the alternating pair, so it cannot occur on a path ending at a large label. Thus the entire original arc consists of one large parent followed by an opposite dyadic ladder b,2b,... . Cutting the retained label list at the first next large label partitions it into full physical arcs; recursion consumes every arc, including zero-net arcs and arcs crossing the original seam.")),
                        Paragraph(Text("At every large parent the same original unsigned potential lies in [A+1,N-A-1]. Choose one physical large label minimizing u and rotate the complete original cycle to that label. Every arc starts at h = u_parent-u_min and ends at the next such height. These are one common boundary vector, of width at most N-2A-2. An arc's total is exactly its endpoint potential difference, so an internal reordering creates no offset at the next join.")),
                        Paragraph(Text("For a positive parent a and a negative ladder of length j and total magnitude S=(2^j-1)b, put n=min(2^j-1,floor(h/b)). Select the original ladder labels indicated by the binary digits of n before the parent, and place the complementary labels after it. The recursive binary selection returns both lists together with a permutation proof and selected mass nb; it never replaces physical labels by distinct numerical values. Before the parent, heights decrease from h to h-nb. Afterwards they decrease from h-nb+a to the original endpoint h+a-S. If h is at least S, the peak is that endpoint. Otherwise 0 <= h-nb <= b-1, so the peak is at most a+b-1. Because a>A, this is N-a-1 <= B. Negative parents use the same construction at reflected height B-h. The two actual endpoints and this one capacity inequality control every intermediate height for either sign or zero arc net.")),
                        Paragraph(Text("If no large label exists, take a label of maximum magnitude m. If m is zero, every source value is zero. Otherwise an inner successor would have magnitude 2m, contradicting maximality. An outer successor forces N <= 3m <= 3A <= N, hence N=3A and m=A. The deterministic original path is then trapped in the alternating values A and -A. Its unsigned potentials lie in [A,2A]; rotating at a minimum potential gives all heights in [0,A], which is contained in [0,B]. This retains all repeated occurrences and covers zero within the universal quantifiers.")),
                        Paragraph(Text("The external target is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. That conjecture requests C=(N-1)/2 for every positive k. The theorem here is a separate repository development of the support bound B for k>=3; it makes no literature-novelty claim and does not settle the full conjecture or its preregistration #20057. For k>=4, B>C, and the all-source capacity-C gap remains open. The k=1 and k=2 boundary cases are outside this theorem."))),
                    DescribeRole.Theorem)), []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("circle-width-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Nat() => Name("Nat");
    private static Formula Int() => Name("Int");
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
