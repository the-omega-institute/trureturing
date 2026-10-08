using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class EndAmplitudeCosineSumZerosDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For natural numbers a < b < c with a and c odd, b even and gcd(a, b, c) = 1, the cosine sum N(t) = (b^2 - a^2)(c^2 - a^2)(c^2 - b^2) + b^2 c^2 (c^2 - b^2) cos(at) + a^2 c^2 (c^2 - a^2) cos(bt) + a^2 b^2 (b^2 - a^2) cos(ct) has a zero in the open interval (0, pi) if and only if a is not 1. For a = 1 it is positive on [0, pi); for a >= 3 it takes a negative value in (0, pi).",
        H("Zeros of the end amplitude numerator of a seven-site chain"),
        Blocks(
            Node("numerator", "The amplitude numerator", NumeratorFormula(),
                Paragraph(Text("The cosine sum N(a, b, c; t) attached to the seven frequencies 0, a, -a, b, -b, c, -c. For a chain of seven sites whose spectrum is a positive multiple of {0, a, -a, b, -b, c, -c}, with first-site spectral weights proportional to the reciprocals of the products of the gaps to the other frequencies, the first-site amplitude is a positive multiple of N at a rescaled time: clearing the denominators of 1/(a^2 b^2 c^2) + cos(at)/(a^2 (b^2 - a^2)(c^2 - a^2)) + cos(bt)/(b^2 (b^2 - a^2)(c^2 - b^2)) + cos(ct)/(c^2 (c^2 - a^2)(c^2 - b^2)) gives N. The chains in question are those with perfect state transfer between the end sites and symmetric spectrum studied by Escobar and Garcia, arXiv:2507.18767; this module treats N as a function in its own right and does not formalise the chain.")),
                "amplitudeNumerator", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("positive", "Positivity for a = 1", PositiveFormula(),
                Paragraph(Text("Put t = pi - 2 theta with theta in (0, pi/2]. Since cos(k (pi - 2 theta)) = (-1)^k (1 - 2 sin^2(k theta)) and the constant term of N equals C1 - C2 + C3 with C1 = b^2 c^2 (c^2 - b^2), C2 = a^2 c^2 (c^2 - a^2), C3 = a^2 b^2 (b^2 - a^2), the parities of a, b, c give N(pi - 2 theta) = 2 B(theta), B = C1 sin^2(a theta) - C2 sin^2(b theta) + C3 sin^2(c theta). For a = 1, writing psi(x) = (sin x / x)^2, u = b theta, v = c theta and sin^2(k theta) = (k theta)^2 psi(k theta), one finds B = b^2 c^2 ((psi(theta) - psi(u))(v^2 - theta^2) - (psi(theta) - psi(v))(u^2 - theta^2)), which is positive because the chord slope of psi in the squared variable from the base point theta in (0, pi/2] is strictly decreasing and theta < u < v."),
                    Ref("D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt")),
                "amplitudeNumerator_pos", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("negative", "A negative value for a >= 3", NegativeFormula(),
                Paragraph(Text("The numerator is even in t, so it suffices to find theta in (0, pi), theta different from pi/2, with B(theta) < 0 in the notation of the previous statement; the time is |pi - 2 theta|. Note C2 > C3 > 0. If a does not divide b, take theta = pi j / a with 0 < j < a, which is never pi/2 because a is odd: then sin(a theta) = 0 and B = -C2 s_b(j) + C3 s_c(j) with s_m(j) = sin^2(pi j m / a). For m not divisible by a the sum of s_m(j) over the a residues j is a/2, by the closed form of the sum of cos(2 pi j m / a), and for m divisible by a every s_m(j) vanishes; so the sum of s_b is a/2 and the sum of s_c is at most a/2. Hence some residue j has s_b(j) > 0 and s_c(j) <= s_b(j) (otherwise s_b <= s_c termwise with strict inequality at j = 1); necessarily j is not 0, and B <= -(C2 - C3) s_b(j) < 0. If a divides b, write b = a beta with beta >= 2; then a does not divide c because gcd(a, b, c) = 1 and a >= 3, so d = gcd(a, c) is a proper divisor of the odd number a, whence 3d <= a and d < c. Choose 0 < l < c with a l congruent to d modulo c and take theta = pi l / c, which is not pi/2 because c is odd. Then sin(c theta) = 0, sin^2(a theta) = sin^2 x and sin^2(b theta) = sin^2(beta x) with x = pi d / c, and B = a^2 c^2 (beta^2 (c^2 - b^2) sin^2 x - (c^2 - a^2) sin^2(beta x)). Put y = beta x; then 0 < y < pi/3 because 3 beta d <= b < c. From sin y > y - y^3/6 > 0 and 0 < sin x < x one gets sin^2 y > y^2 (1 - y^2/3) >= beta^2 sin^2 x (1 - y^2/3), and (c^2 - a^2)(1 - y^2/3) - (c^2 - b^2) = (b^2 - a^2) - (c^2 - a^2) y^2/3 >= 0 since (c^2 - a^2) y^2/3 <= pi^2 beta^2 d^2/3 <= 16 beta^2 a^2/27 <= (beta^2 - 1) a^2 for beta >= 2. Hence B < 0.")),
                "exists_amplitudeNumerator_neg", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("zeros", "The numerator vanishes in (0, pi) exactly when a is not 1", ZeroFormula(),
                Paragraph(Text("The numerator is continuous and N(0) > 0, all four terms being positive at t = 0. If a is not 1 then a >= 3 because a is odd, the previous statement gives a time t1 in (0, pi) with N(t1) < 0, and the intermediate value theorem gives a zero in (0, t1). If a = 1 then b > 1 and the positivity statement excludes zeros in (0, pi). For a seven-site chain with perfect state transfer at its earliest time and symmetric spectrum, the condition a = 1 says that every positive eigenvalue is an integer multiple of the smallest one, and a zero of N in (0, pi) is a time before the transfer time at which the first-site amplitude vanishes; this is the cosine-sum form of the conjecture closing Escobar and Garcia, arXiv:2507.18767. The source states that conjecture; the statement here is about the function N only, the reduction of the chain to N is not part of this module, and the statement was registered before its proof in issue #14487 of this repository.")),
                "amplitudeNumerator_zero_iff", DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, DocumentBlock body,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("endamplitude-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(body), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Plus2(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minus2(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Sq(Formula value) => new Formula.Power(value, D(2));

    private static Formula AndAlso(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);

    private static Formula Numerator(Formula a, Formula b, Formula c, Formula t) =>
        Call("amplitudeNumerator", a, b, c, t);

    private static Formula GcdOne(Formula a, Formula b, Formula c) =>
        Equal(Call("gcd", Call("gcd", a, b), c), D(1));

    private static Formula Parities(Formula a, Formula b, Formula c) =>
        AndAlso(AndAlso(Call("Odd", a), Call("Even", b)), Call("Odd", c));

    private static Formula Ordered(Formula a, Formula b, Formula c) =>
        AndAlso(Less(a, b), Less(b, c));

    private static Formula OpenInterval(Formula t) => AndAlso(Less(D(0), t), Less(t, Pi));

    private static Formula NumeratorFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), t = F.Id("t");
        Formula ba = Minus2(Sq(b), Sq(a)), ca = Minus2(Sq(c), Sq(a)), cb = Minus2(Sq(c), Sq(b));
        Formula constant = Mul(Mul(ba, ca), cb);
        Formula first = Mul(Mul(Mul(Sq(b), Sq(c)), cb), Call("cos", Mul(a, t)));
        Formula second = Mul(Mul(Mul(Sq(a), Sq(c)), ca), Call("cos", Mul(b, t)));
        Formula third = Mul(Mul(Mul(Sq(a), Sq(b)), ba), Call("cos", Mul(c, t)));
        return Disp(Equal(Numerator(a, b, c, t), Plus2(Plus2(Plus2(constant, first), second), third)));
    }

    private static Formula PositiveFormula()
    {
        Formula b = F.Id("b"), c = F.Id("c"), t = F.Id("t");
        Formula parameters = AndAlso(AndAlso(AndAlso(Call("Even", b), Call("Odd", c)),
            Less(D(1), b)), Less(b, c));
        Formula times = AndAlso(LessEq(D(0), t), Less(t, Pi));
        Formula body = All("t", Reals(), Implies(times, Less(D(0), Numerator(D(1), b, c, t))));
        return Disp(All("b", Naturals(), All("c", Naturals(), Implies(parameters, body))));
    }

    private static Formula NegativeFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), t = F.Id("t");
        Formula parameters = AndAlso(AndAlso(AndAlso(Parities(a, b, c), LessEq(D(3), a)),
            Ordered(a, b, c)), GcdOne(a, b, c));
        Formula witness = Some("t", Reals(),
            AndAlso(OpenInterval(t), Less(Numerator(a, b, c, t), D(0))));
        return Disp(All("a", Naturals(), All("b", Naturals(), All("c", Naturals(),
            Implies(parameters, witness)))));
    }

    private static Formula ZeroFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), t = F.Id("t");
        Formula parameters = AndAlso(AndAlso(Parities(a, b, c), Ordered(a, b, c)), GcdOne(a, b, c));
        Formula zero = Some("t", Reals(),
            AndAlso(OpenInterval(t), Equal(Numerator(a, b, c, t), D(0))));
        return Disp(All("a", Naturals(), All("b", Naturals(), All("c", Naturals(),
            Implies(parameters, Iff(zero, NotEqual(a, D(1))))))));
    }
}
