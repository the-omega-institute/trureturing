using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QuditPartialEstimationTradeoffDocument : IScribeDocumentDefinition
{
    private static LibraryNoteRef Note => LibraryNoteRef.Create("D5/L/QuantumChannels/mista2006partialestimation");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal occupation operators and the exact qudit partial-estimation frontier.",
        H("QuditPartialEstimationTradeoff"), Blocks(
            Describe.Lean(DescribeId.Create("quditpartialestimationtradeoff-claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.claim"),
                H("claim"), StatementSource.FromAuthor(Disp(Equal(Q("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Note), Blocks(Paragraph(Text("Page 1, Introduction: \"Moreover, we also conjecture that the optimal fidelity trade-off for an ensemble of N identical pure states of a d-level system has the form\" (2). N and d range over natural numbers with N at least one and d at least two. G ranges over the stated closed real interval. The source equation is encoded in squared form. The set contains exactly the literal PSD-seed output scores with trace D(N,d) and estimation score G; it uses RF and RG from the Section II operators. The arbitrary-instrument covariance reduction is not separately asserted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quditpartialestimationtradeoff-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result"),
                H("result"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Note), Blocks(Paragraph(Text("Every allowed estimation score has a positive semidefinite seed attaining the curve, and every seed at that score lies below it. Occupation-block dominance proves the upper bound; the normalized reference-block vector gives attainment."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mista-fiurasek-2006-qudit-partial-estimation"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody() => All("N", NatType, All("d", NatType, Implies(Leq(D(1), Id("N")), Implies(Leq(D(2), Id("d")), All("G", RealType, Implies(Leq(Frac(Typed(Id("N"), RealType), Sub(Add(Typed(Id("N"), RealType), Typed(Id("d"), RealType)), D(1))), Id("G")), Implies(Leq(Id("G"), Frac(Add(Typed(Id("N"), RealType), D(1)), Add(Typed(Id("N"), RealType), Typed(Id("d"), RealType)))), Q("IsGreatest", SetOf("F", RealType, ExistsAt("chi", Q("Matrix", Q("Prod", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("N"))), Q("Fin", Id("d"))), Q("Prod", SubtypeOf("n", Arrow(Q("Fin", Id("d")), NatType), Equal(SumAt("i", Q("Fin", Id("d")), App(Id("n"), Id("i"))), Id("N"))), Q("Fin", Id("d"))), ComplexType), And(Q("Matrix.PosSemidef", Id("chi")), And(Equal(Q("Matrix.trace", Id("chi")), Typed(Q("Nat.choose", Sub(Add(Id("N"), Id("d")), D(1)), Sub(Id("d"), D(1))), ComplexType)), And(Equal(Q("Complex.re", Q("Matrix.trace", Mul(Id("chi"), Q("RG", Id("N"), Id("d"))))), Id("G")), Equal(Id("F"), Q("Complex.re", Q("Matrix.trace", Mul(Id("chi"), Q("RF", Id("N"), Id("d"))))))))))), Add(Frac(D(1), Add(Typed(Id("N"), RealType), Typed(Id("d"), RealType))), Square(Add(Q("Real.sqrt", Mul(Sub(Typed(Id("d"), RealType), D(1)), Sub(Frac(Add(Typed(Id("N"), RealType), D(1)), Add(Typed(Id("N"), RealType), Typed(Id("d"), RealType))), Id("G")))), Q("Real.sqrt", Mul(Typed(Id("N"), RealType), Sub(Id("G"), Frac(Typed(Id("N"), RealType), Add(Typed(Id("N"), RealType), Typed(Id("d"), RealType)))))))))))))))));

    private static Formula Id(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula NatType => Seq(Mathbb, Grp(Id("N")));
    private static Formula RealType => Seq(Mathbb, Grp(Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Q(string name, params Formula[] args)
    {
        if (name == "Matrix.blockDiagonal'")
        {
            Formula symbol = Seq(Q("Matrix.blockDiagonal"), Apos);
            return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
        }
        Formula[] words = name.Split('.').Select(part => (Formula)Seq(Operatorname, Grp(Id(part)))).ToArray();
        Formula head = Seq(words.SelectMany((part, index) => index == 0 ? new[] {part} : new[] {Dot, part}).ToArray());
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsAt(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula SumAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, domain)), Parenthesized(body));
    private static Formula SubtypeOf(string name, Formula domain, Formula body) => Seq(OpenBrace, Id(name), Colon, Sp, domain, Sp, Slash, Slash, Sp, body, CloseBrace);
    private static Formula SetOf(string name, Formula domain, Formula body) => Seq(OpenBrace, Id(name), Colon, Sp, domain, Sp, Bar, Sp, body, CloseBrace);
}
