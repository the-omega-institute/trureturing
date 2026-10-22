using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class EntanglementDistanceBellDiagonalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/vesperinibelhadjaissafranzosi2023entanglement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entanglement distance of a Bell-diagonal state is not twice its squared concurrence.",
        H("Bell-diagonal entanglement distance refutation"),
        Blocks(
            Node("onSite", "One-site operators", OnSiteFormula(),
                "For a two-qubit product basis, onSite acts by U on the selected coordinate and by the identity on the other coordinate. The two branches are selected by μ = 0 and μ ≠ 0.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("sitePauli", "Pauli observables on one site", SitePauliFormula(),
                "sitePauli chooses X, Y or Z from the Fin(3) label i and places that Pauli on site μ through onSite. The Pauli matrices are the existing X, Y and Z matrices.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("siteQCD", "The variational site quantum-correlation distance", SiteQcdFormula(),
                "The site QCD is the real part of the trace of σ squared minus the supremum of the real trace quadratic form over real unit vectors n. Each Pauli coefficient n i is embedded into the complex matrices by Complex.ofReal. This is the one-site variational form of the source QCD.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rotated", "The locally rotated mixture", RotatedFormula(),
                "For a finite ensemble, rotated applies the SU(2) matrix selected for each component on site μ, conjugates that component, and averages with the real weights embedded in ℂ.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ED", "Entanglement distance", EdFormula(),
                "ED takes the infimum over finite decompositions into positive semidefinite trace-one matrices and sums the two inner infima of the site QCD over families of local SU(2) rotations. The mixture constraint reconstructs ρ exactly. The sum includes both sites, μ = 0 and μ = 1, matching the source's twice-squared-concurrence normalization; the printed ED equation starts its site sum at μ = 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bellProjector", "The four Bell projectors", BellProjectorFormula(),
                "The four projectors are written entrywise in the product basis, in the order (|00⟩ + |11⟩)/√2, (|00⟩ − |11⟩)/√2, (|01⟩ + |10⟩)/√2 and (|01⟩ − |10⟩)/√2. These are the four Bell states in the source's Bell-diagonal decomposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bellDiagonal", "Bell-diagonal states", BellDiagonalFormula(),
                "For nonnegative weights summing to one, the weighted sum of the four Bell projectors is a Bell-diagonal state. The displayed definition also admits arbitrary real weights, embedded into the complex matrix algebra. This is the Bell-diagonal family used in the source.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("concurrence", "Concurrence of a Bell-diagonal state", ConcurrenceFormula(),
                "For nonnegative Bell-diagonal weights summing to one, concurrence is the positive part of twice the largest weight minus one. This is the standard Bell-diagonal concurrence formula of Bennett, DiVincenzo, Smolin and Wootters (1996). The displayed definition extends the same expression to arbitrary real weights.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("claim", "The Bell-diagonal entanglement-distance claim", ClaimFormula(),
                "The source reports numerical evidence for the identity ED = 2 times squared concurrence on Bell-diagonal states, with its figure plotting ED/2. The claim requires this identity for every nonnegative weight vector on the four Bell states whose weights sum to one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A two-qubit counterexample", Disp(new Formula.Not(F.Id("claim"))),
                "Take the Bell-diagonal state with weights (16/25, 9/25, 0, 0). It is the equal mixture of the projectors onto the two nonorthogonal pure states (|00⟩ + q₊|11⟩)/√2 and (|00⟩ + q₋|11⟩)/√2, where q₊ = (7 + 24i)/25 and q₋ = (7 − 24i)/25. On either site, the SU(2) rotations diag((4 + 3i)/5,(4 − 3i)/5) and diag((3 + 4i)/5,(3 − 4i)/5) take the respective projectors to the first two Bell projectors. The rotated mixture is therefore diag(1/2,0,0,1/2). Both site QCD values are zero, hence ED is at most zero, while twice the squared concurrence is 98/625. Thus ED ≤ 0 < 98/625. These states and rotations give a counterexample to the claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo())
        ),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("vesperini-ed-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name)
    {
        var parts = name.Split('.');
        var items = new List<Formula> { Operatorname, Grp(F.Id(parts[0])) };
        for (var i = 1; i < parts.Length; i++)
        {
            var part = parts[i];
            items.Add(Dot);
            var stem = part.EndsWith("'", StringComparison.Ordinal) ? part[..^1] : part;
            var pieces = stem.Split('_');
            for (var piece = 0; piece < pieces.Length; piece++)
            {
                if (piece > 0) items.Add(Underscore);
                items.Add(piece > 0 ? Grp(F.Id(pieces[piece])) : F.Id(pieces[piece]));
            }
            if (part.EndsWith("'", StringComparison.Ordinal)) items.Add(Apos);
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);

    private static Formula At(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, body);

    private static Formula AllG(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);

    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(F.Id(name), type), Comma, Sp, body);

    private static Formula SomeG(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);

    private static Formula SomeAnon(Formula type, Formula body) =>
        SomeG(new Formula.Placeholder(), type, body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Neg(Formula value) => new Formula.Negate(value);

    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula RealToComplex(Formula value) =>
        Cast(Call("Complex.ofReal", value), Complex());

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Matrix(Formula rows, Formula cols, Formula field) => Call("Matrix", rows, cols, field);
    private static Formula TwoQubit() => Parenthesized(Seq(Fin(D(2)), Sp, Times, Sp, Fin(D(2))));
    private static Formula TwoQubitMatrix() => Matrix(TwoQubit(), TwoQubit(), Complex());
    private static Formula OneQubitMatrix() => Matrix(Fin(D(2)), Fin(D(2)), Complex());
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Sp, Colon, Sp, domain)), Sp, body);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Lambda2(Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(F.Id("i"), type), Sp, Mapsto, Sp,
            Parenthesized(Seq(LambdaLower, Sp, Typed(F.Id("j"), type), Sp, Mapsto, Sp, body))));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
            Parenthesized(yes), Sp, Named("else"), Sp, Parenthesized(no)));
    private static Formula ApplyIf(Formula condition, Formula yes, Formula no) => If(condition, yes, no);
    private static Formula Re(Formula value) => Call("Complex.re", value);
    private static Formula Trace(Formula value) => Call("Matrix.trace", value);
    private static Formula Adj(Formula value) => Call("Matrix.conjTranspose", value);
    private static Formula Scale(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Field(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula HalfComplex(bool negative = false) =>
        Div(negative ? Neg(Cast(D(1), Complex())) : Cast(D(1), Complex()), Cast(D(2), Complex()));
    private static Formula SupPrime(Formula p) =>
        Call("Finset.sup'", Call("Finset.univ"), Call("Finset.univ_nonempty"), p);

    private static Formula OnSiteFormula()
    {
        Formula μ = Mu, U = F.Id("U"), i = F.Id("i"), j = F.Id("j");
        Formula index = TwoQubit();
        Formula first = Call("Matrix.of", Lambda2(index,
            If(Eqn(Field(i, 2), Field(j, 2)),
                At(At(U, Field(i, 1)), Field(j, 1)), Cast(D(0), Complex()))));
        Formula second = Call("Matrix.of", Lambda2(index,
            If(Eqn(Field(i, 1), Field(j, 1)),
                At(At(U, Field(i, 2)), Field(j, 2)), Cast(D(0), Complex()))));
        return Disp(AllG(μ, Fin(D(2)), All("U", OneQubitMatrix(),
            Eqn(Call("onSite", μ, U), If(Eqn(μ, D(0)), first, second)))));
    }

    private static Formula SitePauliFormula()
    {
        Formula μ = Mu, i = F.Id("i");
        Formula pauli = ApplyIf(Eqn(i, D(0)), Call("pauliMatrix", Named("Pauli.X")),
            ApplyIf(Eqn(i, D(1)), Call("pauliMatrix", Named("Pauli.Y")), Call("pauliMatrix", Named("Pauli.Z"))));
        return Disp(AllG(μ, Fin(D(2)), All("i", Fin(D(3)),
            Eqn(Call("sitePauli", μ, i), Call("onSite", μ, pauli)))));
    }

    private static Formula SiteQcdFormula()
    {
        Formula μ = Mu, σ = SigmaLower, n = F.Id("n"), i = F.Id("i"), x = F.Id("x");
        Formula pauliSum = SumOver(i, Fin(D(3)), Scale(RealToComplex(At(n, i)),
            Call("sitePauli", μ, i)));
        Formula quadratic = Re(Trace(Mul(Mul(Mul(σ, pauliSum), σ), pauliSum)));
        Formula unit = Eqn(SumOver(i, Fin(D(3)), Pow(At(n, i), D(2))), D(1));
        Formula set = SetOf("x", Real(), Some("n", Arrow(Fin(D(3)), Real()),
            And(unit, Eqn(x, quadratic))));
        return Disp(AllG(μ, Fin(D(2)), AllG(σ, TwoQubitMatrix(),
            Eqn(Call("siteQCD", μ, σ), Sub(Re(Trace(Mul(σ, σ))), Call("sSup", set))))));
    }

    private static Formula RotatedFormula()
    {
        Formula k = F.Id("k"), μ = Mu, p = F.Id("p"), ρs = Seq(Rho, Grp(F.Id("s"))), U = F.Id("U"), j = F.Id("j");
        Formula unitary = Call("Matrix.specialUnitaryGroup", Fin(D(2)), Complex());
        Formula local = Call("onSite", μ, Cast(Call("Subtype.val", At(U, j)), OneQubitMatrix()));
        Formula term = Scale(RealToComplex(At(p, j)),
            Mul(Mul(local, At(ρs, j)), Adj(local)));
        Formula body = Eqn(Call("rotated", μ, p, ρs, U), SumOver(j, Fin(k), term));
        return Disp(All("k", Nat(), AllG(μ, Fin(D(2)),
            All("p", Arrow(Fin(k), Real()), AllG(ρs, Arrow(Fin(k), TwoQubitMatrix()),
                All("U", Arrow(Fin(k), unitary), body))))));
    }

    private static Formula EdFormula()
    {
        Formula ρ = Rho, x = F.Id("x"), k = F.Id("k"), p = F.Id("p"), ρs = Seq(Rho, Grp(F.Id("s")));
        Formula j = F.Id("j"), μ = Mu, U = F.Id("U"), y = F.Id("y");
        Formula unitary = Call("Matrix.specialUnitaryGroup", Fin(D(2)), Complex());
        Formula inner = SetOf("y", Real(), Some("U", Arrow(Fin(k), unitary),
            Eqn(y, Call("siteQCD", μ, Call("rotated", μ, p, ρs, U)))));
        Formula value = SumOver(μ, Fin(D(2)), Call("sInf", inner));
        Formula positivity = All("j", Fin(k), Leq(D(0), At(p, j)));
        Formula total = Eqn(SumOver(j, Fin(k), At(p, j)), D(1));
        Formula state = All("j", Fin(k), And(Call("Matrix.PosSemidef", At(ρs, j)), Eqn(Trace(At(ρs, j)), Cast(D(1), Complex()))));
        Formula mixture = Eqn(SumOver(j, Fin(k), Scale(RealToComplex(At(p, j)), At(ρs, j))), ρ);
        Formula existential = SetOf("x", Real(), Some("k", Nat(), Some("p", Arrow(Fin(k), Real()),
            SomeG(ρs, Arrow(Fin(k), TwoQubitMatrix()),
                SomeAnon(positivity, SomeAnon(total, SomeAnon(state, SomeAnon(mixture,
                    Eqn(x, value)))))))));
        return Disp(AllG(ρ, TwoQubitMatrix(), Eqn(Call("ED", ρ), Call("sInf", existential))));
    }

    private static Formula BellProjectorFormula()
    {
        Formula α = Alpha, i = F.Id("i"), j = F.Id("j"), pair = TwoQubit();
        Formula zero = Call("D5.S3.QuantumBounds.CHSHWitness.bellDensity", i, j);
        Formula p00 = Pair(D(0), D(0)), p11 = Pair(D(1), D(1)), p01 = Pair(D(0), D(1)), p10 = Pair(D(1), D(0));
        Formula branch(Formula a, Formula b, Formula c, Formula d) =>
            If(And(Eqn(i, a), Eqn(j, a)), HalfComplex(),
                If(And(Eqn(i, b), Eqn(j, b)), HalfComplex(),
                    If(And(Eqn(i, a), Eqn(j, b)), c,
                        If(And(Eqn(i, b), Eqn(j, a)), d, Cast(D(0), Complex())))));
        Formula minus00 = branch(p00, p11, HalfComplex(true), HalfComplex(true));
        Formula plus01 = branch(p01, p10, HalfComplex(), HalfComplex());
        Formula minus01 = branch(p01, p10, HalfComplex(true), HalfComplex(true));
        Formula body = Eqn(Call("bellProjector", α), Call("Matrix.of", Lambda2(pair,
            If(Eqn(α, D(0)), zero,
                If(Eqn(α, D(1)), minus00,
                    If(Eqn(α, D(2)), plus01, minus01))))));
        return Disp(AllG(α, Fin(D(4)), body));
    }

    private static Formula BellDiagonalFormula()
    {
        Formula p = F.Id("p"), α = Alpha;
        return Disp(All("p", Arrow(Fin(D(4)), Real()),
            Eqn(Call("bellDiagonal", p), SumOver(α, Fin(D(4)),
                Scale(RealToComplex(At(p, α)), Call("bellProjector", α))))));
    }

    private static Formula ConcurrenceFormula()
    {
        Formula p = F.Id("p");
        Formula sup = SupPrime(p);
        Formula value = Call("max", D(0), Sub(Mul(D(2), sup), D(1)));
        return Disp(All("p", Arrow(Fin(D(4)), Real()), Eqn(Call("concurrence", p), value)));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), α = Alpha;
        Formula nonnegative = AllG(α, Fin(D(4)), Leq(D(0), At(p, α)));
        Formula normalized = Eqn(SumOver(α, Fin(D(4)), At(p, α)), D(1));
        Formula equality = Eqn(Call("ED", Call("bellDiagonal", p)),
            Mul(D(2), Pow(Call("concurrence", p), D(2))));
        Formula body = All("p", Arrow(Fin(D(4)), Real()), Imp(nonnegative, Imp(normalized, equality)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
