using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeParentFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula r = V("r"), w = V("word"), n = V("n"), L = V("L"), B = V("B");
        Formula k = Add(r, Num(4)), T = Pow(Num(2), r);
        Formula t = Sub(Mul(Num(11), Pow(Num(2), Sub(r, Num(1)))), Num(1));
        Formula P = Sub(Mul(Num(8), T), Num(11)), C = Sub(Mul(Num(8), T), Num(1));
        Formula source = Call("actualSource", k, t);
        Formula height = Call("sum", Call("map", source, Call("take", n, w)));
        Formula complete = Eq(Call("toFinset", w), Name("univ"));
        Formula good = Ex("word", Call("List", Call("Fin", k)), And(Call("Nodup", w), complete,
            Q(And(Le(Num(0), height), Le(height, P), Le(Num(0), height), Le(height, C)),
                ("n", Name("Nat")))));
        Formula lower = Q(Imp(complete, Q(Imp(Q(And(Le(L, height), Le(height, B)),
            ("n", Name("Nat"))), Le(P, Sub(B, L))), ("L", Name("Int")), ("B", Name("Int")))),
            ("word", Call("List", Call("Fin", k))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An infinite family of actual centered doubling sources has an exactly optimal physical permutation width, ten below its half-modulus capacity.",
            H("A sharp three-parent source family"),
            Blocks(
                Describe.Lean(DescribeId.Create("sharp-actual-family"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeParentFamily.sharp_actual_family"),
                    H("Every label, every prefix, and the matching lower bound"),
                    StatementSource.FromAuthor(Disp(Q(Imp(Le(Num(4), r), And(good, lower)),
                        ("r", Name("Nat"))))), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural r>=4, set T=2^r, k=r+4, N=16T-1, C=8T-1 and natural t=11*2^(r-1)-1. The source is exactly SourceWidth.actualSource(k,t), on all Fin(k) occurrence labels. There exists a distinct complete physical-label list whose integer prefix sums, for every natural prefix length including lengths beyond its end, lie both in [0,P] and [0,C], where P=8T-11. Conversely, for any complete occurrence list and any integer interval [L,B] containing every prefix sum, P<=B-L. The lower bound even allows repeated labels in that other list; completeness forces the positive step P to occur.")),
                        Paragraph(Text("Put U=T/2. Centered doubling gives the exact source sequence (11U-1,-10U-1,12U-3,-8U-5,16U-11,-21,-42,...,-21*2^(r-2)). The proof computes the first five branches and then inducts through the actual negative dyadic children. The modulus is 32U-1, and the bound 4*2^j<=U keeps every required internal child doubling in its centered branch. No coprimality assumption or replacement of occurrences by numerical values is used.")),
                        Paragraph(Text("Let H=5U-10 and delta=(-H) mod 21, so 0<=delta<=20 and H+delta is divisible by 21. The children have total mass 21(U-1). The integer n=(H+delta)/21 satisfies 0<=n<U=2^(r-1). Binary digit selection partitions the original physical child list into before and after, with selected mass 21n=H+delta and complementary mass P-delta. Both lists consist solely of negative actual occurrences. Thus each segment decreases monotonically between its displayed endpoints.")),
                        Paragraph(Text("At height delta the first two full arcs have heights delta, delta+11U-1, delta+U-2, delta+13U-5, delta+H. The selected children then reach zero; the third parent reaches P; the complementary children return to delta. Rotation at that attained zero is explicit: execute the third parent, the complementary children, the first two full arcs, and the selected children. All labels occur exactly once, and the closed path starts and ends at zero. The first-two-arc peak is 13U-5+delta. When r>=5, U>=16 and P-(13U-5)=3U-6>=42>20. At r=4, U=8, H=30, delta=12 and that peak is 111<=117=P. These bounds prove all intermediate prefixes, including both closed walls.")),
                        Paragraph(Text("For the lower bound, locate physical label 4 in any complete list. Its actual value is P. The sums immediately before and after that occurrence differ by P, so any containing interval must have width at least P. This argument combines with the constructed word to give the exact optimum for this family. It does not assert that maximum absolute step is the optimum for arbitrary centered sources.")),
                        Paragraph(Text("The source problem is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. The dynamic construction is a special-family result with a compatible binary split and movable base. It supplies no arbitrary-source choice of sign orders, arc partitions or compatible bases. The universal half-modulus forcing step and full C3.1 remain open. No literature novelty or official uniqueness claim is made."))),
                    DescribeRole.Theorem)), []));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
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
