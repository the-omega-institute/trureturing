using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GraftLocalBehaviorLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primitive Fibonacci state that hits zero has exactly one zero phase at each prime-power precision.",
        H("Local Fibonacci Zero Phases"),
        Blocks(Describe.Lean(
            DescribeId.Create("graft-primitive-hit-phase"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels.primitive_hit_phase"),
            H("The zero phase of a primitive state"),
            StatementSource.FromAuthor(PhaseFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let p be any prime and m be any natural number. The step S(a,b)=(b,a+b) acts on pairs over Z/(p^m)Z. A pair is primitive when at least one coordinate is a unit. Let r be the least positive index with p^m dividing the Fibonacci number F(r), with F(0)=0 and F(1)=1.")),
                Paragraph(Text("If the first coordinate of S^t(x) is zero, then the first coordinate of S^k(x) is zero exactly when k and t have the same residue modulo r. Both t and k are arbitrary natural numbers, including zero. There is no restriction to odd primes and no assumption that the zero rank grows at every precision.")),
                Paragraph(Text("The coordinates of a primitive pair remain coprime under the step. At a zero hit, the second coordinate is consequently a unit. Forward from this hit, the first coordinate is F(d) times that unit, so its zeros are precisely the multiples of r. A finite common return period transfers this criterion to times before the chosen hit."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(Formula a, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, a, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PhaseFormula()
    {
        Formula p = F.Id("p"), m = F.Id("m"), x = F.Id("x"), t = F.Id("t"), k = F.Id("k");
        Formula n = Pow(p, m), r = Call("zeroRank", n);
        Formula first(Formula i) => Call("fst", Call("iterate", F.Id("S"), i, x));
        Formula primitive = Seq(Call("IsUnit", Call("fst", x)), Sp, Lor, Sp,
            Call("IsUnit", Call("snd", x)));
        Formula conclusion = Seq(Par(Equal(first(k), D(0))), Sp, Iff, Sp,
            Par(Equal(Call("mod", k, r), Call("mod", t, r))));
        return Disp(All(p, N, All(m, N, Seq(
            Call("Prime", p), Sp, Implies, Sp,
            All(x, Pow(Call("ZMod", n), D(2)), Seq(Par(primitive), Sp, Implies, Sp,
                All(t, N, All(k, N, Seq(Equal(first(t), D(0)), Sp, Implies, Sp, conclusion)))))))));
    }
}
