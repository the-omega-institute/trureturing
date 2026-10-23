using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ThermalProcessSelfDualFactorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/mazurekhorodecki2018decomposability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-level self-dual irreducible extreme thermal process factors into two extreme processes acting on fewer levels, refuting the non-self-duality conjecture.",
        H("A self-dual factorization of an irreducible thermal process"),
        Blocks(
            Node("thermalProcesses", "Thermal processes", ThermalProcessesFormula(),
                "For a natural dimension d and a real Gibbs vector g on Fin d, a thermal process is a matrix T whose columns are stochastic and which preserves g. This is the Gibbs-preserving column-stochastic characterization stated in the source paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("actsOnFewerLevels", "Processes acting on fewer levels", ActsOnFewerLevelsFormula(),
                "A process acts non-trivially on at most d minus one levels when it fixes at least one level k, expressed by the diagonal entry T k k being one. This is the source paper's condition for a process acting on a proper subspace.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("selfDual", "Self-duality", SelfDualFormula(),
                "Self-duality with respect to the Gibbs weights is the detailed-balance relation T i j times g j equals T j i times g i for every pair of levels. It is equivalent to equality with the conjugated transpose in the source paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("irreducible", "Irreducibility", IrreducibleFormula(),
                "Irreducibility reads the phrase not a direct sum as the absence of a nonempty proper set S whose two sides have all cross-block entries zero. Here Sᶜ denotes the complement in the finite level set Fin d.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The non-self-duality conjecture", ClaimFormula(),
                "The source conjectures that an extremal thermal process C on d levels, factored as C = A B with extremal factors each fixing a level, cannot be self-dual when C has no direct-sum decomposition across a nonempty proper set of levels. The formal statement assumes d is at least two, all Gibbs weights are positive and pairwise distinct, and the weight at level zero is maximal.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("thermal-self-dual-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A five-level refutation"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Set d = 5 and use the Gibbs weights (8, 7, 4, 2, 3). Let A be the matrix with rows (0, 1, 0, 1/2, 0), (1/4, 0, 1, 1/2, 0), (1/2, 0, 0, 0, 0), (1/4, 0, 0, 0, 0), (0, 0, 0, 0, 1); it acts on levels 0 through 3 and fixes level 4. Let B have rows (1, 0, 0, 0, 0), (0, 1/7, 1, 1, 0), (0, 1/7, 0, 0, 1), (0, 2/7, 0, 0, 0), (0, 3/7, 0, 0, 0), so it fixes level 0. Their product is C = A B, with rows (0, 2/7, 1, 1, 0), (1/4, 2/7, 0, 0, 1), (1/2, 0, 0, 0, 0), (1/4, 0, 0, 0, 0), (0, 3/7, 0, 0, 0). Each of A, B and C is nonnegative, column-stochastic and preserves the Gibbs weights. Each is extreme by support uniqueness: in a convex combination, every factor has zero entries wherever the matrix has a zero entry, and the column sums together with Gibbs preservation determine all remaining entries uniquely. The non-loop support edges of C are 0–1, 0–2, 0–3 and 1–4, so C is irreducible. Finally, C satisfies detailed balance: C times the diagonal matrix of the Gibbs weights is symmetric. Thus the factorization satisfies every hypothesis of claim while its conclusion fails."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mazurek-horodecki-2018-thermal-process-self-dual-factorization-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("thermal-self-dual-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type,
            Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type,
            Parenthesized(body));
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula MatrixMulVec(Formula matrix, Formula vector) =>
        QCall("Matrix", "mulVec", matrix, vector);
    private static Formula MatrixType(Formula d) => Call("Matrix", Fin(d), Fin(d), Real());
    private static Formula ExtremePoints(Formula set) =>
        QCall("Set", "extremePoints", Real(), set);
    private static Formula FunctionInjective(Formula f) =>
        QCall("Function", "Injective", f);
    private static Formula FinsetType(Formula d) => Call("Finset", Fin(d));
    private static Formula FinZero(Formula d) => Parenthesized(Seq(D(0), Colon, Fin(d)));
    private static Formula Complement(Formula s) => new Formula.Power(s, F.Id("c"));
    private static Formula Nonempty(Formula s) => QCall("Finset", "Nonempty", s);
    private static Formula BlockCross(Formula i, Formula j, Formula s) =>
        Or(And(Member(i, s), Not(Member(j, s))),
            And(Not(Member(i, s)), Member(j, s)));

    private static Formula ThermalProcessesFormula()
    {
        Formula d = F.Id("d"), g = F.Id("g"), T = F.Id("T");
        Formula colStochastic = QCall("Matrix", "colStochastic", Real(), Fin(d));
        Formula body = Member(T, colStochastic);
        body = And(body, Equal(MatrixMulVec(T, g), g));
        return Disp(All("d", Nat(), All("g", Arrow(Fin(d), Real()),
            All("T", MatrixType(d), Iff(Member(T, Call("thermalProcesses", g)), body)))));
    }

    private static Formula ActsOnFewerLevelsFormula()
    {
        Formula d = F.Id("d"), T = F.Id("T"), k = F.Id("k");
        Formula body = Some("k", Fin(d), Equal(App(T, k, k), D(1)));
        return Disp(All("d", Nat(), All("T", MatrixType(d),
            Iff(Call("actsOnFewerLevels", T), body))));
    }

    private static Formula SelfDualFormula()
    {
        Formula d = F.Id("d"), g = F.Id("g"), T = F.Id("T");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula equation = Equal(
            new Formula.Binary(App(T, i, j), FormulaBinaryOperator.Multiply, App(g, j)),
            new Formula.Binary(App(T, j, i), FormulaBinaryOperator.Multiply, App(g, i)));
        Formula body = All("i", Fin(d), All("j", Fin(d), equation));
        return Disp(All("d", Nat(), All("g", Arrow(Fin(d), Real()),
            All("T", MatrixType(d), Iff(Call("selfDual", g, T), body)))));
    }

    private static Formula IrreducibleFormula()
    {
        Formula d = F.Id("d"), T = F.Id("T"), S = F.Id("S");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula cross = BlockCross(i, j, S);
        Formula implication = Imp(cross, Equal(App(T, i, j), D(0)));
        Formula block = All("i", Fin(d), All("j", Fin(d), implication));
        Formula witness = Some("S", FinsetType(d), And(Nonempty(S),
            And(Nonempty(Complement(S)), block)));
        return Disp(All("d", Nat(), All("T", MatrixType(d),
            Iff(Call("irreducible", T), Not(witness)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), g = F.Id("g");
        Formula i = F.Id("i"), A = F.Id("A"), B = F.Id("B"), C = F.Id("C");
        Formula positivity = All("i", Fin(d), Less(D(0), App(g, i)));
        Formula maximal = All("i", Fin(d), Leq(App(g, i), App(g, FinZero(d))));
        Formula conclusion = Not(Call("selfDual", g, C));
        Formula hypotheses =
            Imp(Member(A, ExtremePoints(Call("thermalProcesses", g))),
                Imp(Member(B, ExtremePoints(Call("thermalProcesses", g))),
                    Imp(Member(C, ExtremePoints(Call("thermalProcesses", g))),
                        Imp(Equal(C, new Formula.Binary(A, FormulaBinaryOperator.Multiply, B)),
                            Imp(Call("actsOnFewerLevels", A),
                                Imp(Call("actsOnFewerLevels", B),
                                    Imp(Call("irreducible", C), conclusion)))))));
        Formula body = All("d", Nat(), Imp(Leq(D(2), d),
            All("g", Arrow(Fin(d), Real()),
                Imp(positivity, Imp(FunctionInjective(g),
                    Imp(maximal, All("A", MatrixType(d), All("B", MatrixType(d),
                        All("C", MatrixType(d), hypotheses)))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
