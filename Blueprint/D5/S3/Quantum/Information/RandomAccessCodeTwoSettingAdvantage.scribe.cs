using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class RandomAccessCodeTwoSettingAdvantageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/ambainis2024racadvantage");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n and d at least two, a d-dimensional random access code with two projective measurement settings strictly outperforms every classical strategy with shared randomness.",
        H("Two measurement settings suffice for quantum advantage in random access codes"),
        Blocks(
            Paragraph(Text(
                "Fin(n) denotes the indices 0 through n minus one. A word x is a function "
                    + "from Fin(n) to Fin(d). Alice receives a uniformly chosen word and sends "
                    + "one d-dimensional system; Bob receives a uniformly chosen index j and "
                    + "guesses x(j). Complex conjugation is denoted by an overline. "
                    + "All sums range over the displayed finite domains.")),
            Node("deterministic-value", "deterministicValue", "The deterministic classical value",
                DeterministicFormula(),
                "The encoder E sends one alphabet symbol and the decoder D returns a symbol "
                    + "for each received symbol and query. The indicator is one when its "
                    + "condition holds and zero otherwise. The factor 1/(n d^n) averages "
                    + "over words and queries, as in Section 2, Eq. (4), and Section 3.1 "
                    + "of the source. This real-valued definition has no positivity "
                    + "hypotheses on n or d; division by zero has its usual totalized field value zero."),
            Node("classical-strategy", "ClassicalStrategy", "A classical strategy with shared randomness",
                ClassicalStrategyFormula(),
                "The displayed record consists of a type Lambda, a chosen finite enumeration "
                    + "of Lambda, weights p, and encoder and decoder families E and D. "
                    + "Each weight is nonnegative and their sum is one. For a shared value "
                    + "lambda, E(lambda) and D(lambda) form a deterministic strategy. "
                    + "The record fields are Lambda, finite, weight, nonneg, total, encode "
                    + "and decode, with p, E and D denoting weight, encode and decode. "
                    + "This is the finite shared-randomness description in Section 3.1."),
            Node("classical-value", "classicalValue", "The value of a classical mixture",
                ClassicalValueFormula(),
                "The value is the weighted average of the deterministic values. Here "
                    + "weight(S), encode(S), decode(S) and Lambda(S) denote the corresponding "
                    + "fields of S. Shared randomness therefore forms a convex combination "
                    + "of deterministic success probabilities, as in Section 3.1."),
            Node("quantum-value", "quantumValue", "The quantum value for two settings",
                QuantumFormula(),
                "For query j, Bob uses setting s(j); the measurement vector for a correct "
                    + "outcome is column x(j) of U(s(j)). The inner sum is the inner product "
                    + "of that column with psi(x), conjugating the column entries. Its squared "
                    + "modulus is the Born probability when psi(x) is a unit vector and the "
                    + "two matrices are unitary. These conditions are imposed in claim; "
                    + "quantumValue itself is defined for arbitrary vectors and matrices. "
                    + "The normalization is again that of Section 2, Eq. (4)."),
            Node("claim", "claim", "Strict advantage for every pair of parameters",
                ClaimFormula(),
                "For every n and d at least two, one encoding by complex unit vectors, "
                    + "two unitary matrices and one setting choice per query simultaneously "
                    + "give a value strictly greater than that of every finite classical "
                    + "mixture. The unitary group consists of d by d complex unitary matrices. "
                    + "This states the general quantum-advantage question and its two-setting "
                    + "resource requirement from Section 5 of the source."),
            Describe.Lean(
                DescribeId.Create("rac-two-setting-advantage-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A construction giving strict advantage"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a fixed classical decoder, the best encoder chooses a row with "
                            + "the largest number of matches with the word. If a decoder column "
                            + "omits a symbol, replace one occurrence of a repeated symbol by "
                            + "that missing symbol. Holding the other input coordinates fixed, "
                            + "the scores for the repeated and missing symbols together do not "
                            + "decrease; all other scores stay the same. Each exchange reduces "
                            + "the total number of missing symbols, so eventually every column "
                            + "is a permutation. Relabeling the alphabet separately at each "
                            + "coordinate then gives identity decoding. Majority encoding "
                            + "attains the resulting classical optimum C(n,d), equal to "
                            + "1/(n d^n) times the sum over words x of the largest number of "
                            + "occurrences of a single symbol in x. Convex combinations cannot "
                            + "exceed this optimum, in agreement with the classical benchmark "
                            + "of Ambainis, Kravchenko, Sazim, Bae and Rai.")),
                    Paragraph(Text(
                        "Take U(0) = I and U(1) = F, where F has first two by two block "
                            + "[[3/5, 4/5], [4/5, -3/5]] and is the identity on the remaining "
                            + "coordinates. The columns of F are an orthonormal rotated basis. "
                            + "Use this basis for the last query and the standard basis for "
                            + "every other query. For a fixed prefix z of length n minus one, "
                            + "let N(i) count symbol i, let m be the largest count and let M "
                            + "be the set of maximisers. If f(b) is column b of F, project "
                            + "f(b) onto the coordinates in M and normalize the projection. "
                            + "When the projection is zero, use any standard basis vector "
                            + "with index in M. The score on word (z,b), summed over queries, "
                            + "is m plus the squared norm of that projection. Summing over b "
                            + "gives d m + |M|, exactly the sum of the largest symbol counts "
                            + "of the words (z,b). Averaging over prefixes proves that this "
                            + "baseline encoding has value C(n,d).")),
                    Paragraph(Text(
                        "Change only the encoding of the all-zero word 0^n to "
                            + "(2n e(0) + e(1))/sqrt(4n^2 + 1). Its old score, summed over "
                            + "queries, is n - 1 + 9/25. The new score is "
                            + "((n - 1) 4n^2 + (6n + 4)^2/25)/(4n^2 + 1). "
                            + "The gain is (23n + 32)/(25(4n^2 + 1)), which is strictly "
                            + "positive. The average value therefore increases by this gain "
                            + "divided by n d^n, while all other word scores are preserved. "
                            + "The resulting two-setting quantum value exceeds C(n,d) and "
                            + "hence the value of every classical strategy."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rac-two-setting-advantage-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Finite(Formula size) => Call("Fin", size);
    private static Formula Words(Formula n, Formula d) => Arrow(Finite(n), Finite(d));
    private static Formula Encoder(Formula n, Formula d) => Arrow(Words(n, d), Finite(d));
    private static Formula Decoder(Formula n, Formula d) => Arrow(Finite(d), Arrow(Finite(n), Finite(d)));
    private static Formula States(Formula n, Formula d) => Arrow(Words(n, d), Arrow(Finite(d), Complexes()));
    private static Formula Matrices(Formula d) => Call("Matrix", Finite(d), Finite(d), Complexes());
    private static Formula Settings() => Finite(D(2));
    private static Formula MatrixFamily(Formula d) => Arrow(Settings(), Matrices(d));
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));
    private static Formula AverageFactor(Formula n, Formula d) =>
        new Formula.Fraction(D(1), Parenthesized(Multiply(n, new Formula.Power(d, n))));

    private static Formula DeterministicFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), e = F.Id("E"), decoder = F.Id("D");
        Formula x = F.Id("x"), j = F.Id("j");
        Formula indicator = Seq(new Formula.Subscript(Named("indicator"),
            Parenthesized(Equal(At(At(decoder, At(e, x)), j), At(x, j)))));
        Formula value = Multiply(AverageFactor(n, d), SumOver(x, Words(n, d),
            SumOver(j, Finite(n), indicator)));
        return All(n, Naturals(), All(d, Naturals(), All(e, Encoder(n, d),
            All(decoder, Decoder(n, d), Equal(Call("deterministicValue", n, d, e, decoder), value)))));
    }

    private static Formula ClassicalStrategyFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), p = F.Id("p"), l = LambdaLower;
        Formula e = F.Id("E"), decoder = F.Id("D");
        Formula record = Seq(OpenBrace, Sp,
            Typed(Lambda, Named("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", Lambda), CloseBracket, Comma, Sp,
            Typed(p, Arrow(Lambda, Reals())), Comma, Sp,
            Typed(e, Arrow(Lambda, Encoder(n, d))), Comma, Sp,
            Typed(decoder, Arrow(Lambda, Decoder(n, d))), Sp, Mid, Sp,
            And(All(l, Lambda, LE(D(0), At(p, l))), Equal(SumOver(l, Lambda, At(p, l)), D(1))),
            Sp, CloseBrace);
        return All(n, Naturals(), All(d, Naturals(), Equal(Call("ClassicalStrategy", n, d), record)));
    }

    private static Formula ClassicalValueFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), s = F.Id("S"), l = LambdaLower;
        Formula term = Multiply(At(Call("weight", s), l), Call("deterministicValue", n, d,
            At(Call("encode", s), l), At(Call("decode", s), l)));
        return All(n, Naturals(), All(d, Naturals(), All(s, Call("ClassicalStrategy", n, d),
            Equal(Call("classicalValue", s), SumOver(l, Call("Lambda", s), term)))));
    }

    private static Formula QuantumFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), u = F.Id("U"), s = F.Id("s");
        Formula x = F.Id("x"), j = F.Id("j"), k = F.Id("k");
        Formula entry = At(At(u, At(s, j)), k, At(x, j));
        Formula amplitude = SumOver(k, Finite(d), Multiply(Conjugate(entry), At(At(Psi, x), k)));
        Formula value = Multiply(AverageFactor(n, d), SumOver(x, Words(n, d),
            SumOver(j, Finite(n), new Formula.Power(new Formula.Absolute(amplitude), D(2)))));
        return All(n, Naturals(), All(d, Naturals(), All(Psi, States(n, d),
            All(u, MatrixFamily(d), All(s, Arrow(Finite(n), Settings()),
                Equal(Call("quantumValue", n, d, Psi, u, s), value))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), u = F.Id("U"), s = F.Id("s");
        Formula x = F.Id("x"), k = F.Id("k"), i = F.Id("i"), strategy = F.Id("S");
        Formula unit = All(x, Words(n, d), Equal(SumOver(k, Finite(d),
            Multiply(Conjugate(At(At(Psi, x), k)), At(At(Psi, x), k))), D(1)));
        Formula unitary = All(i, Settings(), new Formula.Relation(At(u, i),
            FormulaRelationOperator.MemberOf, Call("unitaryGroup", Finite(d), Complexes())));
        Formula advantage = All(strategy, Call("ClassicalStrategy", n, d),
            new Formula.Relation(Call("classicalValue", strategy), FormulaRelationOperator.LessThan,
                Call("quantumValue", n, d, Psi, u, s)));
        Formula construction = Some(Psi, States(n, d), Some(u, MatrixFamily(d),
            Some(s, Arrow(Finite(n), Settings()), And(unit, And(unitary, advantage)))));
        Formula proposition = All(n, Naturals(), All(d, Naturals(),
            Implies(LE(D(2), n), Implies(LE(D(2), d), construction))));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(proposition));
    }
}
