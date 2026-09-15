using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class HeadGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cumulative square-root increments realize the head occupation kernel in a small memory span.",
        H("Head Occupation Gram Construction"),
        Blocks(Describe.Lean(
            DescribeId.Create("head-gram-realization"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/HeadGram.head_gram_realization"),
            H("The explicit Gram family, recurrence, and span"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let sigma be finite, let a assign a natural capacity to every letter, and " +
                    "choose any head h in sigma. Box(a) contains r with 0<=r(i)<=a(i). " +
                    "Write M(r)=|r|!/product(i,r(i)!), where |r| is the total occupation. " +
                    "Two profiles have the same tail when they agree away from h. Define " +
                    "K(r,s)=M(min(r,s)) for equal tails and K(r,s)=0 otherwise; min is coordinatewise.")),
                Paragraph(Text(
                    "For a tail b and natural j, let m(b,j)=M(j,b). Its value is a fixed positive " +
                    "tail multinomial times choose(j+|b|,|b|), so it is nondecreasing in j. " +
                    "Put delta(b,0)=m(b,0) and delta(b,j)=m(b,j)-m(b,j-1) for j>0. " +
                    "In the complex Euclidean space indexed by bounded tails and head levels " +
                    "0 through a(h), the vector chi(r) has coordinate sqrt(delta(b,k)) when " +
                    "b is the tail of r and k<=r(h), and zero otherwise. All roots are nonnegative real roots.")),
                Paragraph(Text(
                    "Let H be the complex span of these vectors. Their inner product is K(r,s): " +
                    "different tails have disjoint support, and equal tails give a telescoping sum " +
                    "through min(r(h),s(h)). Thus K is the actual positive semidefinite Gram matrix. " +
                    "For nonzero r and s the recurrence sums K(r-e(i),s-e(i)) over letters with " +
                    "both occupations positive. Simultaneous lowering preserves tail equality, " +
                    "and the multinomial erasure identity proves the recurrence at the coordinatewise minimum.")),
                Paragraph(Text(
                    "All pure-head vectors coincide with chi(0). Removing the a(h) nonzero " +
                    "pure-head profiles from the generating family leaves a spanning family of " +
                    "size product(i,a(i)+1)-a(h). This proves the dimension upper bound. " +
                    "If a(h)>0, chi(0)=chi(e(h)), so the nonterminal vectors alone span H. " +
                    "Zero capacities and equal maximizing head capacities require no exclusions."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a = F.Id("a"), h = F.Id("h"), r = F.Id("r"), s = F.Id("s");
        Formula box = Call("Box", a), memory = Call("H", a, h);
        Formula bound = Seq(Call("product", Call("aPlusOne", a)), Sp, Minus, Sp, Call("a", h));
        Formula gram = Seq(Forall, Sp, r, Comma, s, Colon, Sp, box, Comma, Sp,
            Call("inner", Call("chi", r), Call("chi", s)), Sp, Eq, Sp, Call("K", r, s));
        Formula recurrence = Seq(Forall, Sp, r, Comma, s, Colon, Sp, Call("Profiles", F.Id("sigma")),
            Comma, Sp, r, Sp, Neq, Sp, D(0), Comma, Sp, s, Sp, Neq, Sp, D(0), Sp, Implies, Sp,
            Call("K", r, s), Sp, Eq, Sp, Call("commonPositiveLoweringSum", r, s));
        Formula span = Seq(D(0), Sp, Lt, Sp, Call("a", h), Sp, Implies, Sp,
            Call("span", Call("nonterminalChi", a, h)), Sp, Eq, Sp, memory);
        return Disp(Seq(Forall, Sp, a, Colon, Sp, F.Id("sigma"), Sp, To, Sp, F.Id("Nat"), Comma,
            Sp, h, Colon, Sp, F.Id("sigma"), Comma, Esc,
            Grp(gram), Sp, Land, Esc, Grp(recurrence), Sp, Land, Esc,
            Call("finrank", F.Id("Complex"), memory), Sp, Leq, Sp, bound,
            Sp, Land, Esc, Grp(span)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
