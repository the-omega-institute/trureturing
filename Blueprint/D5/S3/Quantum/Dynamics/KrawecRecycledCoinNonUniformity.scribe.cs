using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class KrawecRecycledCoinNonUniformityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/krawec2015history");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noninteger memory parameter gives a nonuniform recycled-coin return average.",
        H("Krawec recycled-coin nonuniformity"), Blocks(
            Node("angle", "Conditional coin angle", "angle", AngleFormula(),
                "Equation (4) assigns angle π/4 when the inactive coin is zero and π(1+φ)/4 when it is one. The definition accepts every real memory parameter.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coin-flip", "Conditional coin flip", "coinFlip", CoinFlipFormula(),
                "Equations (3) and (4) apply the real matrix with rows (cos θ, sin θ) and (sin θ, −cos θ) to the active coin. FreeSpectrahedronFeasibilityWitness.X3 is that real matrix; Complex.ofReal casts each entry to a complex scalar before multiplication by an amplitude. Positions belong to ZMod d and coin indices to Fin 2 × Fin 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("shift", "Conditional cyclic shift", "shift", ShiftFormula(),
                "The shift following Equation (4) moves basis positions by minus one for active coin zero and plus one for active coin one. On amplitudes, the value at n therefore comes from n+1 or n−1, respectively. Addition and both displacement values are in ZMod d.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("swap", "Exchange of the coins", "swap", SwapFormula(),
                "Equation (5) exchanges the inactive and active coin indices and preserves the position.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("u", "One step of the walk", "U", StepFormula(),
                "Equation (6) first flips the active coin, then shifts the position, and finally exchanges the coins.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("initial", "State localized at zero", "initial", InitialFormula(),
                "The initial states in §III.B place an arbitrary coin amplitude at position zero. Every other position has zero amplitude; normalization is expressed separately by unitCoin.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("p", "Position probability after iteration", "p", ProbabilityFormula(),
                "Equation (7) sums the squared complex amplitudes over all four coin indices after t steps. The notation f^[t] means Nat.iterate f t, including the identity at t=0. The initial state is localized at position zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("avg", "Finite Cesàro average", "avg", AverageFormula(),
                "The finite average in Equation (8) sums probabilities at times 1 through T. Finset.range T indexes this sum by t=0 through T−1, with the probability evaluated at t+1. The denominator is the real cast of T; at T=0 the empty sum and real division give zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("exceptional", "The conjectured exceptional parameters", "exceptional", ExceptionalFormula(),
                "Sections III.B and IV distinguish two sets of memory parameters: {0,1,2,4,5,6} when twelve divides the cycle size, and {0,2,4,6} otherwise. Each set consists of real numbers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("unit-coin", "Normalized coin state", "unitCoin", UnitCoinFormula(),
                "The initial coin states in §III.B are normalized: the sum of squared complex amplitudes over Fin 2 × Fin 2 equals one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Krawec's uniformity conjecture", "claim", ClaimFormula(),
                "Sections III.B and IV conjecture uniformity outside the stated exceptional parameters. For every cycle size d≥2, every φ in [0,8) outside exceptional d, every normalized coin state initially at position zero, and every position n, the finite Cesàro averages are asserted to converge to 1/d as T tends to infinity. Krawec reports numerical checks for d≤300 and leaves a proof as an open problem.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The uniformity conjecture is false"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For cycle size 12, take the memory parameter 4·arccos((√2/2)·((√5−1)/2))/π−1. It lies strictly between zero and one, outside the exceptional set. Fourier blocks for momenta zero and two share an eigenvalue whose eigenspaces have nonzero coin overlap. The mean ergodic theorem gives convergent Cesàro averages, and a strict surplus in the sum of the four return averages forces some normalized computational basis coin to have return limit greater than 1/12. This contradicts the uniformity conjecture in Krawec's §IV."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krawec-2015-recycled-coin-uniformity-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula AngleFormula() => All("phi", Reals(), All("i", FinTwo(),
        Equal(LocalCall("angle", X("phi"), X("i")),
            Call("ite", Equal(X("i"), Typed(Num(0), FinTwo())),
                Fraction(Qualified("Real", "pi"), Num(4)),
                Fraction(Multiply(Qualified("Real", "pi"),
                    Parenthesized(Add(Num(1), X("phi")))), Num(4))))));

    private static Formula CoinFlipFormula() => All("d", Naturals(), All("phi", Reals(),
        All("psi", Amplitudes(), All("n", Positions(), All("c", Coins(),
            Equal(LocalCall("coinFlip", X("phi"), X("psi"), X("n"), X("c")),
                SumOver("b", FinTwo(), Multiply(
                    At(Qualified("Complex", "ofReal"), At(
                        Qualified("D5", "S3", "Quantum", "Measurement",
                            "FreeSpectrahedronFeasibilityWitness", "X3"),
                        LocalCall("angle", X("phi"), First(X("c"))), Second(X("c")), X("b"))),
                    At(X("psi"), X("n"), Pair(First(X("c")), X("b")))))))))));

    private static Formula ShiftFormula() => All("d", Naturals(), All("psi", Amplitudes(),
        All("n", Positions(), All("c", Coins(),
            Equal(LocalCall("shift", X("psi"), X("n"), X("c")),
                At(X("psi"), Add(X("n"), Call("ite",
                    Equal(Second(X("c")), Typed(Num(0), FinTwo())),
                    Typed(Num(1), Positions()), Negate(Typed(Num(1), Positions())))), X("c")))))));

    private static Formula SwapFormula() => All("d", Naturals(), All("psi", Amplitudes(),
        All("n", Positions(), All("c", Coins(),
            Equal(LocalCall("swap", X("psi"), X("n"), X("c")),
                At(X("psi"), X("n"), Pair(Second(X("c")), First(X("c")))))))));

    private static Formula StepFormula() => All("d", Naturals(), All("phi", Reals(),
        All("psi", Amplitudes(), Equal(LocalCall("U", X("phi"), X("psi")),
            LocalCall("swap", LocalCall("shift", LocalCall("coinFlip", X("phi"), X("psi"))))))));

    private static Formula InitialFormula() => All("d", Naturals(), All("alpha", CoinAmplitudes(),
        All("n", Positions(), All("c", Coins(),
            Equal(LocalCall("initial", X("alpha"), X("n"), X("c")),
                Call("ite", Equal(X("n"), Typed(Num(0), Positions())),
                    At(X("alpha"), X("c")), Typed(Num(0), Complexes())))))));

    private static Formula ProbabilityFormula() => All("d", Naturals(), All("phi", Reals(),
        All("alpha", CoinAmplitudes(), All("n", Positions(), All("t", Naturals(),
            Equal(LocalCall("p", X("phi"), X("alpha"), X("n"), X("t")),
                SumOver("c", Coins(), At(Qualified("Complex", "normSq"),
                    At(new Formula.Power(Parenthesized(LocalCall("U", X("phi"))),
                            Seq(OpenBracket, X("t"), CloseBracket)),
                        Typed(LocalCall("initial", X("alpha")), Amplitudes()), X("n"), X("c"))))))))));

    private static Formula AverageFormula() => All("d", Naturals(), All("phi", Reals(),
        All("alpha", CoinAmplitudes(), All("n", Positions(), All("T", Naturals(),
            Equal(LocalCall("avg", X("phi"), X("alpha"), X("n"), X("T")),
                Fraction(Seq(new Formula.Subscript(Sum,
                        Member(X("t"), At(Qualified("Finset", "range"), X("T")))), Sp,
                    Parenthesized(LocalCall("p", X("phi"), X("alpha"), X("n"),
                        Add(X("t"), Num(1))))), RealCast(X("T")))))))));

    private static Formula ExceptionalFormula() => All("d", Naturals(),
        Equal(LocalCall("exceptional", X("d")), Call("ite",
            new Formula.Relation(Num(12), FormulaRelationOperator.Divides, X("d")),
            Typed(new Formula.SetLiteral([Num(0), Num(1), Num(2), Num(4), Num(5), Num(6)]), RealSet()),
            Typed(new Formula.SetLiteral([Num(0), Num(2), Num(4), Num(6)]), RealSet()))));

    private static Formula UnitCoinFormula() => All("alpha", CoinAmplitudes(),
        Equivalence(LocalCall("unitCoin", X("alpha")),
            Equal(SumOver("c", Coins(), At(Qualified("Complex", "normSq"),
                At(X("alpha"), X("c")))), Typed(Num(1), Reals()))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"),
        All("d", Naturals(), Implication(LE(Num(2), X("d")),
            All("phi", Reals(), Implication(
                Member(X("phi"), At(Qualified("Set", "Ico"), Typed(Num(0), Reals()), Num(8))),
                Implication(new Formula.Not(Parenthesized(Member(X("phi"), LocalCall("exceptional", X("d"))))),
                    All("alpha", CoinAmplitudes(), Implication(LocalCall("unitCoin", X("alpha")),
                        All("n", Positions(), At(Qualified("Filter", "Tendsto"),
                            LocalCall("avg", X("phi"), X("alpha"), X("n")),
                            Typed(Qualified("Filter", "atTop"), Call("Filter", Naturals())),
                            Call("nhds", Fraction(Num(1), RealCast(X("d"))))))))))))));

    private static Formula ResultFormula() => new Formula.Not(Parenthesized(Local("claim")));

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Dynamics", "KrawecRecycledCoinNonUniformity", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinTwo() => Call("Fin", Num(2));
    private static Formula Coins() => Parenthesized(Seq(FinTwo(), Sp, Times, Sp, FinTwo()));
    private static Formula Positions() => Call("ZMod", X("d"));
    private static Formula CoinAmplitudes() => Parenthesized(new Formula.TypeArrow(Coins(), Complexes()));
    private static Formula Amplitudes() => Parenthesized(new Formula.TypeArrow(Positions(), CoinAmplitudes()));
    private static Formula RealSet() => Call("Set", Reals());
    private static Formula RealCast(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula First(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Second(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula Pair(Formula first, Formula second) => Parenthesized(Seq(first, Comma, Sp, second));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula SumOver(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(variable), type)), Sp, Parenthesized(body));
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Negate(Formula value) => new Formula.Negate(value);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
