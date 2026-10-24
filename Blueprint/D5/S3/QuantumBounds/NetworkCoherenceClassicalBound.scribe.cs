using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class NetworkCoherenceClassicalBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumBounds/NetworkCoherenceClassicalBound";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/bibakdelsantodakic2024coherence");

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Booleans => Seq(Mathrm, Grp(F.Id("Bool")));
    private static Formula N => F.Id("n");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula R => F.Id("r");
    private static Formula C => F.Id("c");
    private static Formula I => F.Id("i");
    private static Formula Bits => Arrow(Call("Fin", N), Booleans);
    private static Formula LocalLaws => Arrow(Call("Fin", N), Arrow(Booleans, Reals));
    private static Formula StringLaw => Arrow(Parenthesized(Bits), Reals);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Real(byte value) => Typed(D(value), Reals);
    private static Formula Nat(byte value) => Typed(D(value), Naturals);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Mixture => Call("classicalMixture", N, GammaLower, P, Q);
    private static Formula Merit(Formula law) => Call("coherenceMerit", N, law);

    private static Formula ParityDefinition => All(N, Naturals, All(A, Bits,
        Eq(Call("parity", A), new Formula.Modulo(Call("occupationCount", A), Nat(2)))));

    private static Formula MixtureDefinition => All(N, Naturals,
        All(GammaLower, Reals, All(P, LocalLaws, All(Q, LocalLaws,
            Eq(Mixture, Parenthesized(Seq(Typed(A, Bits), Mapsto, Sp,
                Add(Mul(GammaLower, Call("windowLaw", P, A)),
                    Mul(Sub(Real(1), GammaLower), Call("windowLaw", Q, A))))))))));

    private static Formula ParitySum(Formula variable, byte value, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, Bits, Comma, Sp,
            Eq(Call("parity", variable), Nat(value)))), Sp, Parenthesized(body));
    private static Formula PairSum(byte value) => ParitySum(A, value, ParitySum(B, value,
        Call("ite", new Formula.Relation(A, FormulaRelationOperator.NotEqual, B),
            Mul(App(R, A), App(R, B)), Real(0))));
    private static Formula MeritDefinition => All(N, Naturals, All(R, StringLaw,
        Eq(Merit(R), Mul(Div(Real(1), Real(2)),
            new Formula.Absolute(Sub(PairSum(0), PairSum(1)))))));

    private static Formula AttainableValues => Seq(OpenBrace, C, Colon, Sp, Reals, Sp, Mid, Sp,
        Some(GammaLower, Reals, And(
            new Formula.Relation(GammaLower, FormulaRelationOperator.MemberOf,
                App(Seq(Operatorname, Grp(F.Id("Set"), Dot, F.Id("Icc"))), Real(0), Real(1))),
            Some(P, LocalLaws, Some(Q, LocalLaws,
                And(All(I, Call("Fin", N), Call("Probability", App(P, I))),
                    And(All(I, Call("Fin", N), Call("Probability", App(Q, I))),
                        Eq(C, Merit(Mixture)))))))), CloseBrace);
    private static Formula ClaimBody => All(N, Naturals, Imp(Le(Nat(2), N),
        Call("IsGreatest", AttainableValues, Div(Real(1), Real(4)))));
    private static Formula ClaimDefinition => IffFormula(
        Seq(Operatorname, Grp(F.Id("claim"))), ClaimBody);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coherence merit of a mixture of two binary product laws has attainable maximum one quarter for every n at least two.",
        H("The sharp classical network coherence bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity"),
                DeclarationHandle.Create(Module + ".parity"),
                H("Parity of a binary string"),
                StatementSource.FromAuthor(Disp(ParityDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A binary string a assigns a Boolean to each element of Fin n. "
                    + "The occupation count is the natural sum of the values (a i).toNat, "
                    + "where false has value zero and true has value one. Reducing this count "
                    + "modulo two gives parity. The two parity classes are those used in "
                    + "main.tex, lines 263–271, of Quantum coherence in networks."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("classical-mixture"),
                DeclarationHandle.Create(Module + ".classicalMixture"),
                H("A mixture of two product laws"),
                StatementSource.FromAuthor(Disp(MixtureDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each string a, windowLaw p a is the product of p i (a i) over all "
                    + "i in Fin n. The displayed function combines this product with the "
                    + "corresponding product for q, with weights γ and 1 − γ. This is "
                    + "equation (pncl), main.tex, lines 248–253. The function is defined for "
                    + "all real γ and real local functions p and q. It is a probability law "
                    + "when γ lies in the real interval [0,1] and every local function is a "
                    + "probability distribution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherence-merit"),
                DeclarationHandle.Create(Module + ".coherenceMerit"),
                H("The parity coherence merit"),
                StatementSource.FromAuthor(Disp(MeritDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an arbitrary real function r on binary strings, sum r a times r b "
                    + "over ordered pairs of distinct even strings, and subtract the same sum "
                    + "over ordered pairs of distinct odd strings. The merit is half the "
                    + "absolute value of this difference. Each conditional makes the diagonal "
                    + "term zero. Both indices in each sum have the indicated parity. "
                    + "This reads equation (cn) and its explanation in main.tex, lines 263–271, "
                    + "with ordered pairs. For n at least two, a uniform law on the even strings "
                    + "gives the value one half minus two to the power minus n "
                    + "stated at lines 272–276."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The attainable classical maximum"),
                StatementSource.FromAuthor(Disp(ClaimDefinition)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least two, consider all merits of the displayed "
                    + "mixtures with γ in [0,1] and with p i and q i probability distributions "
                    + "on Bool for every i. Probability means that both values are nonnegative "
                    + "and their sum is one. IsGreatest asserts that one quarter belongs to "
                    + "this set and bounds every member from above. This is the reading of "
                    + "the conjecture at main.tex, lines 277–278, for the ordered pair "
                    + "convention and n at least two. At n equal to one, each parity class "
                    + "has one string and the merit is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The sharp bound in every dimension n at least two"),
                StatementSource.FromAuthor(Disp(ClaimBody)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a finite set s, the sum of r a times r b over its distinct "
                        + "ordered pairs equals the square of the sum of r on s minus the "
                        + "sum of the squares. Indeed, each row is r a times the total sum "
                        + "minus (r a) squared. Apply this identity to the two parity classes. "
                        + "The sign χ(a) = (−1) to the power of the natural sum of (a i).toNat "
                        + "is positive on the even class and negative on the odd class. "
                        + "These classes partition all strings. If r sums to one, their "
                        + "masses e and o satisfy e + o = 1, so e squared minus o squared "
                        + "equals e − o. Thus the merit is half of |T − U|, where T is "
                        + "the sum of χ(a) r a and U is the sum of χ(a) (r a) squared.")),
                    Paragraph(Text(
                        "For any local functions w, distributing the product over the "
                        + "Boolean choices shows that the signed sum of the product law "
                        + "is the product of w i false − w i true. The mixture sums to one "
                        + "because each of its two product laws does. Put x i = p i false "
                        + "− p i true and y i = q i false − q i true, and let A and B be "
                        + "their respective products. Let D be the product of (x i + y i)/2. "
                        + "The signed sum T is γA + (1 − γ)B. For the square terms, local "
                        + "normalization gives (p i false) squared minus (p i true) squared "
                        + "equal to x i, and the analogous identity for q. The mixed local "
                        + "difference p i false times q i false minus p i true times q i true "
                        + "equals (x i + y i)/2. Expanding the square of the mixture therefore "
                        + "gives U = γ squared times A + (1 − γ) squared times B "
                        + "+ 2γ(1 − γ)D. Subtraction and nonnegativity of γ(1 − γ) give "
                        + "the merit as γ(1 − γ)|A + B − 2D|/2.")),
                    Paragraph(Text(
                        "To bound the last absolute value, take x i and y i in [−1,1] "
                        + "and induct over a finite set of coordinates s. The expression "
                        + "is zero for the empty set. For the products P, Q and D over s, "
                        + "write F = P + Q − 2D. The induction hypothesis gives |F| ≤ 2. "
                        + "Each factor has absolute value at most one, so |P| and |Q| "
                        + "are at most one and |P − Q| and |Q − P| are at most two. "
                        + "On adding a coordinate i, set u = (1 + x i)/2 and v = (1 + y i)/2. "
                        + "The new expression is uvF + u(1 − v)(P − Q) "
                        + "+ (1 − u)v(Q − P) + (1 − u)(1 − v)(−F). "
                        + "All four coefficients are nonnegative and sum to one. "
                        + "The triangle inequality bounds its absolute value by two, "
                        + "completing the induction and giving the bound over Fin n.")),
                    Paragraph(Text(
                        "Nonnegativity and normalization of p i and q i place x i and "
                        + "y i in [−1,1]. The factorization and the preceding bound give "
                        + "a merit at most γ(1 − γ). The nonnegative square of γ − 1/2 "
                        + "then bounds this by one quarter.")),
                    Paragraph(Text(
                        "To reach the bound, write n = k + 2. Set γ = 1/2, and let p i put "
                        + "all its mass at false. Let q i put all its mass at true when "
                        + "i.val < 2 and at false otherwise. These are probability "
                        + "distributions. The products A and B are both one: the first "
                        + "two factors of B are minus one and all remaining factors are "
                        + "one. The product D is zero because its factor at coordinate "
                        + "zero is zero. Substituting A = B = 1 and D = 0 into the "
                        + "factorization gives exactly one quarter. Hence one quarter "
                        + "is a member of the attainable set; applying the upper bound "
                        + "to any other member proves that it is the greatest member."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bibak-del-santo-dakic-2024-classical-network-coherence-bound"),
                    ResolutionKind.Proved)))));
}
