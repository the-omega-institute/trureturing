using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Walks;

internal sealed class OpenQuantumWalkGamblerHittingTimeRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/jacqlardizabal2017oqwhalfline");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complex reset pair refutes the proposed three-entry formula for gambler's-ruin mean hitting times.",
        H("The open quantum walk hitting-time formula is false"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("oqw-gambler-word-operator"),
                DeclarationHandle.Create(Module + ".wordOperator"),
                H("The time-ordered branch operator"),
                StatementSource.FromAuthor(Disp(WordOperatorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a word of Boolean steps, false selects the left matrix l and true selects the right matrix r. "
                        + "The mapped word is reversed before multiplying, so the last step is the leftmost factor. "
                        + "This is the ordered branch product used in the stopped-path expansion of the open quantum walk (JL_rev2.tex, lines 77–83 and 120–121)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oqw-gambler-position"),
                DeclarationHandle.Create(Module + ".position"),
                H("The integer position after a prefix"),
                StatementSource.FromAuthor(Disp(PositionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Starting at the natural position k, add one for each true step and subtract one for each false step in the first t letters. "
                        + "The integer codomain records leftward motion without truncation. "
                        + "This is the lattice-path position underlying the gambler's-ruin walk (JL_rev2.tex, lines 300–301)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oqw-gambler-first-absorbs"),
                DeclarationHandle.Create(Module + ".firstAbsorbs"),
                H("First absorption at a boundary"),
                StatementSource.FromAuthor(Disp(FirstAbsorbsFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A word first absorbs the walk from k in the interval with boundaries 0 and m when every strict prefix remains strictly between the boundaries and the full word ends at one of them. "
                        + "The prefix condition is the monitoring convention for reaching a boundary for the first time (JL_rev2.tex, lines 1081–1083)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oqw-gambler-absorbed-mass"),
                DeclarationHandle.Create(Module + ".absorbedMass"),
                H("The mass absorbed at a fixed time"),
                StatementSource.FromAuthor(Disp(AbsorbedMassFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Generate all Boolean words of length n by taking sections of n copies of the two-letter block [false,true]. "
                        + "For each word first absorbed at time n, take the real part of the trace of its unnormalized branch matrix W ρ Wᴴ; all other words contribute zero. "
                        + "Summing these terms gives the stopped-path mass used in the source's first-visit probabilities (JL_rev2.tex, lines 1081–1086)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oqw-gambler-mean-hitting-time"),
                DeclarationHandle.Create(Module + ".meanHittingTime"),
                H("The extended mean first absorption time"),
                StatementSource.FromAuthor(Disp(MeanHittingTimeFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Weight the absorbed mass at each natural time n by n, regard the weight as an extended nonnegative real, and sum over all times. "
                        + "The value may be infinite, matching the source's expected time to reach either boundary (JL_rev2.tex, lines 1087–1091)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oqw-gambler-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The proposed dependence on three real matrix entries"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every pair of two-dimensional complex transition matrices satisfying lᴴl + rᴴr = 1 and every m at least 3, the claim supplies two real functions h and j of the two natural indices. "
                        + "The function j is antisymmetric under k ↦ m − k. For every interior starting position and every density matrix, the meanHittingTime is finite and its real value is the affine expression using the two diagonal real entries and the real part of the upper-right entry. "
                        + "This is the formal reading of Remark 5.3 (JL_rev2.tex, lines 1291–1293)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oqw-gambler-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A complex reset pair refutes the claim"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let u = (1, i) and v = (1, −i), indexed by Fin 2, and set l = (1/2) v uᴴ, r = (1/2) v vᴴ, ρ = (1/2) u uᴴ, and σ = (1/2) v vᴴ. "
                            + "Exact entrywise calculation gives lᴴl + rᴴr = 1 and l r = 0. The matrices ρ and σ are positive semidefinite with trace one, so both satisfy IsDensity.")),
                    Paragraph(Text(
                        "The stopped-word calculation uses l r = 0: every first-absorbing word of length at least three contains the consecutive subword [true,false], whose branch operator is l r, so all absorbed masses after time two vanish. "
                            + "At time one only [false] absorbs and contributes trace(l ρ lᴴ); at time two only [true,true] absorbs and contributes trace((r r) ρ (r r)ᴴ). Thus meanHittingTime is the sum of the time-one mass and twice the time-two mass.")),
                    Paragraph(Text(
                        "Substituting the four explicit matrices into that two-step formula gives meanHittingTime l r 3 1 ρ = 1 and meanHittingTime l r 3 1 σ = 2. "
                            + "The three entries used by the claimed affine expression agree for ρ and σ: both diagonal real entries are one half and the real part of the upper-right entry is zero.")),
                    Paragraph(Text(
                        "If the claim held, instantiate it with l, r, m = 3, and k = 1. The common three entries would force the two real mean values to be equal, while the explicit computation makes them 1 and 2. This contradiction proves ¬ claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jacq-lardizabal-2017-oqw-gambler-mean-hitting-time-form"),
                    ResolutionKind.Refuted)))));

    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Walks", "OpenQuantumWalkGamblerHittingTimeRefutation", name);

    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(F.Id(part));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body)));

    private static Formula V(string name) => name == "ρ" ? Rho : F.Id(name);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula ENNReal() => F.Id("ENNReal");
    private static Formula Bool() => Qualified("Bool");
    private static Formula Fin2() => At(Qualified("Fin"), D(2));
    private static Formula Matrix2() => At(Qualified("Matrix"), Fin2(), Fin2(), Complexes());
    private static Formula ListOf(Formula type) => At(Qualified("List"), type);
    private static Formula CastNat(Formula value, Formula target) =>
        Typed(At(Qualified("Nat", "cast"), value), target);

    private static Formula BoolList() => ListOf(Bool());

    private static Formula True() => Qualified("Bool", "true");
    private static Formula False() => Qualified("Bool", "false");

    private static Formula MatrixTrace(Formula value) =>
        At(Qualified("Matrix", "trace"), value);

    private static Formula ConjTranspose(Formula value) =>
        At(Qualified("Matrix", "conjTranspose"), value);

    private static Formula RealPart(Formula value) =>
        At(Qualified("Complex", "re"), value);

    private static Formula ListLiteral(Formula first, Formula second) =>
        Seq(OpenBracket, first, Comma, Sp, second, CloseBracket);

    private static Formula WordOperatorFormula()
    {
        Formula l = F.Id("l"), r = F.Id("r"), w = F.Id("w"), b = F.Id("b");
        Formula choice = At(Qualified("ite"), Equal(b, True()), r, l);
        Formula body = At(Qualified("List", "prod"),
            At(Qualified("List", "reverse"),
                At(Qualified("List", "map"), Lambda("b", Bool(), choice), w)));
        return All("l", Matrix2(), All("r", Matrix2(), All("w", BoolList(),
            Equal(At(Local("wordOperator"), l, r, w), body))));
    }

    private static Formula PositionFormula()
    {
        Formula k = F.Id("k"), w = F.Id("w"), t = F.Id("t"), b = F.Id("b");
        Formula step = At(Qualified("ite"), Equal(b, True()),
            Typed(D(1), Integers()), Negate(Typed(D(1), Integers())));
        Formula mapped = At(Qualified("List", "map"), Lambda("b", Bool(), step),
            At(Qualified("List", "take"), t, w));
        Formula total = At(Qualified("List", "sum"), mapped);
        return All("k", Naturals(), All("w", BoolList(), All("t", Naturals(),
            Equal(At(Local("position"), k, w, t),
                Add(CastNat(k, Integers()), total)))));
    }

    private static Formula FirstAbsorbsFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), w = F.Id("w"), t = F.Id("t");
        Formula prefix = All("t", Naturals(), Implies(
            LessThan(t, At(Qualified("List", "length"), w)),
            And(LessThan(Typed(D(0), Integers()), At(Local("position"), k, w, t)),
                LessThan(At(Local("position"), k, w, t), CastNat(m, Integers())))));
        Formula endpoint = Or(
            Equal(At(Local("position"), k, w, At(Qualified("List", "length"), w)), Typed(D(0), Integers())),
            Equal(At(Local("position"), k, w, At(Qualified("List", "length"), w)), CastNat(m, Integers())));
        return All("m", Naturals(), All("k", Naturals(), All("w", BoolList(),
            Equal(At(Local("firstAbsorbs"), m, k, w), And(prefix, endpoint)))));
    }

    private static Formula AbsorbedMassFormula()
    {
        Formula l = F.Id("l"), r = F.Id("r"), m = F.Id("m"), k = F.Id("k"), rho = V("ρ"), n = F.Id("n");
        Formula w = F.Id("w");
        Formula branch = At(Qualified("ite"), At(Local("firstAbsorbs"), m, k, w),
            RealPart(MatrixTrace(Multiply(Multiply(At(Local("wordOperator"), l, r, w), rho),
                ConjTranspose(At(Local("wordOperator"), l, r, w))))),
            Typed(D(0), Reals()));
        Formula mapped = At(Qualified("List", "map"), Lambda("w", BoolList(), branch),
            At(Qualified("List", "sections"),
                At(Qualified("List", "replicate"), n, ListLiteral(False(), True()))));
        Formula body = At(Qualified("List", "sum"), mapped);
        return All("l", Matrix2(), All("r", Matrix2(), All("m", Naturals(), All("k", Naturals(),
            All("ρ", Matrix2(), All("n", Naturals(),
                Equal(At(Local("absorbedMass"), l, r, m, k, rho, n), body)))))));
    }

    private static Formula MeanHittingTimeFormula()
    {
        Formula l = F.Id("l"), r = F.Id("r"), m = F.Id("m"), k = F.Id("k"), rho = V("ρ"), n = F.Id("n");
        Formula weight = Multiply(CastNat(n, ENNReal()),
            At(Qualified("ENNReal", "ofReal"), At(Local("absorbedMass"), l, r, m, k, rho, n)));
        Formula series = At(Qualified("tsum"), Lambda("n", Naturals(), weight));
        return All("l", Matrix2(), All("r", Matrix2(), All("m", Naturals(), All("k", Naturals(),
            All("ρ", Matrix2(), Equal(At(Local("meanHittingTime"), l, r, m, k, rho), series))))));
    }

    private static Formula ClaimFormula()
    {
        Formula l = F.Id("l"), r = F.Id("r"), m = F.Id("m"), k = F.Id("k"), rho = V("ρ");
        Formula h = F.Id("h"), j = F.Id("j");
        Formula norm = Equal(Add(Multiply(ConjTranspose(l), l), Multiply(ConjTranspose(r), r)),
            Typed(D(1), Matrix2()));
        Formula antisym = All("k", Naturals(), Implies(
            LessThanOrEqual(Typed(D(1), Naturals()), k),
            Implies(LessThanOrEqual(k, Subtract(m, D(1))),
                Equal(At(At(j, m), k), Negate(At(At(j, m), Subtract(m, k)))))));
        Formula densityConclusion = And(
            NotEqual(At(Local("meanHittingTime"), l, r, m, k, rho), Qualified("top")),
            Equal(At(Qualified("ENNReal", "toReal"), At(Local("meanHittingTime"), l, r, m, k, rho)),
                Add(Add(Add(Typed(D(1), Reals()), Multiply(At(At(h, m), Subtract(m, k)), RealPart(At(At(rho, D(0)), D(0))))),
                    Multiply(At(At(h, m), k), RealPart(At(At(rho, D(1)), D(1))))),
                    Multiply(At(At(j, m), k), RealPart(At(At(rho, D(0)), D(1)))))));
        Formula density = All("k", Naturals(), Implies(
            LessThanOrEqual(Typed(D(1), Naturals()), k),
            Implies(LessThanOrEqual(k, Subtract(m, D(1))),
                All("ρ", Matrix2(), Implies(
                    At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), rho),
                    densityConclusion)))));
        Formula functionType = new Formula.TypeArrow(Naturals(),
            new Formula.TypeArrow(Naturals(), Reals()));
        Formula witnesses = Some("h", functionType,
            Some("j", functionType,
                And(antisym, density)));
        return All("l", Matrix2(), All("r", Matrix2(), Implies(norm,
            All("m", Naturals(), Implies(LessThanOrEqual(Typed(D(3), Naturals()), m), witnesses)))));
    }

}
