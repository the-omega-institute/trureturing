using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.RandomWalks;

internal sealed class HarmonicSquareDifferencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/lippnermangoubi2015harmonic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every order of the normalized Laplacian of a harmonic square is a finite average of ordered mixed-difference squares.",
        H("Harmonic squares and all orders of mixed differences"),
        Blocks(
            Node("mean", "The actual nearest-neighbour mean", "translationMean", MeanFormula(),
                DescribeRole.Definition,
                "For a natural d, the lattice is the additive group Fin d to Z. A direction is a pair (i,b) in Fin d times Bool. Its step has coordinate +1 at i when b is true, -1 at i when b is false, and zero elsewhere. Thus there are exactly 2d labels. The displayed denominator is real. Write P for translationMean d and L=P-I for laplacian d. Harmonic H means the equality PH=H of entire real functions. Positive dimension is required in the theorem, so the normalization is nonzero."),
            Node("mixed", "Ordered words and the empty composition", "mixedDifference", MixedFormula(),
                DescribeRole.Definition,
                "A word of length k is any function Fin k to Direction d. No injectivity condition is imposed: a direction may occur any number of times, and words with a common endpoint are still different words. Mathlib's fwdDiff a f is the function x mapped to f(x+a)-f(x). mixedDifference composes those operators with the first letter outermost. At k=0 there is exactly one word, the function from the empty type, and its mixed difference is H itself."),
            Describe.Lean(DescribeId.Create("harmonic-square-all-orders"),
                DeclarationHandle.Create(Prefix + "harmonic_square_iterate"),
                H("The mixed-square identity in every order"),
                StatementSource.FromAuthor(IdentityFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let d be any positive natural number and let H be any real function on the whole integer lattice with PH=H. For every natural k and every lattice point x, L iterated k times on the pointwise square of H equals (2d)^(-k) times the sum of the squares of all length-k mixed differences of H at x. There is no boundedness, growth, periodicity, sign or symmetry assumption on H. The order-zero identity is H(x)^2=H(x)^2, with coefficient one and the single empty word.")),
                    Paragraph(Text("Translation commutes with a forward difference because the lattice addition is commutative. The finite mean therefore commutes with each forward difference, and every mixed difference of H remains harmonic. For a harmonic f, expand (f(x+v)-f(x))^2 and average. The cross term is -2f(x)Pf(x), and the constant term is f(x)^2 because the weights sum to one. Consequently L(f^2) is the average of the forward-difference squares. Apply this identity to every harmonic mixed difference in the length-k sum. Linearity of L and the bijection between a length-(k+1) word and its first letter together with its tail give the next order, with exactly one additional factor (2d)^(-1).")),
                    Paragraph(Text("Every summand and the normalization are nonnegative, so L^k(H^2)(x)>=0 for every k. Since P=I+L and the identity operator commutes with L, the finite binomial formula is P^N(H^2)=sum_(j=0)^N choose(N,j)L^j(H^2). For N>=3, retaining the j=3 term yields P^N(H^2)(x)>=choose(N,3)L^3(H^2)(x). For N<3 the binomial coefficient is zero and the inequality follows from the nonnegative expansion. This is the finite estimate used after equation (2.1) in the constant-Poisson argument.")),
                    Paragraph(Text("Lippner and Mangoubi give this classical identity in arXiv:1312.4550v3, Theorem 2.1, Claim 2.2 and Remark 2.3. Here the mean and the differences are the literal signed-coordinate operators of the integer lattice. The remaining constant-Poisson argument requires the growth estimate for P^N(H^2), the limiting vanishing of third differences and the reconstruction of a quadratic polynomial. Those conclusions and the subsequent classification do not follow from harmonicity alone. The zero-dimensional singleton case is separate and uses no division by d."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("harmonic-square-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name)
    {
        var parts = new List<Formula>();
        foreach (string part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(Seq(Operatorname, Grp(F.Id(part))));
        }
        return Seq([.. parts]);
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Lat(Formula d) => Call("Lattice", d);
    private static Formula Func(Formula d) => new Formula.TypeArrow(Lat(d), Real());
    private static Formula Words(Formula d, Formula k) => Call("Word", d, k);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string x, Formula t, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Weight(Formula d) => new Formula.Fraction(D(1), Mul(D(2), d));
    private static Formula FiniteSum(string x, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(new Formula.Relation(F.Id(x), FormulaRelationOperator.MemberOf, domain)), Sp, body);

    private static Formula MeanFormula()
    {
        Formula d = F.Id("d"), f = F.Id("f"), x = F.Id("x"), v = F.Id("v");
        Formula mean = Mul(Weight(d),
            FiniteSum("v", Call("Direction", d), App(f, Add(x, Call("step", v)))));
        Formula equality = Eq(App(Call("translationMean", d), f, x), mean);
        return Disp(All("d", Nat(), All("f", Func(d), All("x", Lat(d), equality))));
    }

    private static Formula MixedFormula()
    {
        Formula d = F.Id("d"), Hf = F.Id("H"), w = F.Id("w"), k = F.Id("k");
        Formula empty = All("w", Words(d, D(0)), Eq(Call("mixedDifference", D(0), w, Hf), Hf));
        Formula difference = Call("fwdDiff", Call("step", App(w, D(0))),
            Call("mixedDifference", k, Call("Fin.tail", w), Hf));
        Formula recurrence = Eq(Call("mixedDifference", Add(k, D(1)), w, Hf), difference);
        Formula successor = All("k", Nat(), All("w", Words(d, Add(k, D(1))), recurrence));
        return Disp(All("d", Nat(), All("H", Func(d),
            new Formula.Logic(Par(empty), FormulaLogicOperator.And, Par(successor)))));
    }

    private static Formula IdentityFormula()
    {
        Formula d = F.Id("d"), Hf = F.Id("H"), k = F.Id("k"), x = F.Id("x"), w = F.Id("w");
        Formula lhs = Call("Function.iterate", Call("laplacian", d), k, Call("square", Hf), x);
        Formula rhs = Mul(Pow(Weight(d), k), FiniteSum("w", Words(d, k),
            Pow(Call("mixedDifference", k, w, Hf, x), D(2))));
        Formula identity = All("k", Nat(), All("x", Lat(d), Eq(lhs, rhs)));
        Formula harmonic = All("H", Func(d), Imp(Call("Harmonic", Hf), identity));
        return Disp(All("d", Nat(), Imp(Lt(D(0), d), harmonic)));
    }
}
