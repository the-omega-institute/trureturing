using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Repulsion;

internal sealed class FejerNearCollisionBoundDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Zeros/Repulsion/FejerNearCollisionBound.";
    private const string FamilyIdentifier = "g";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed-mode Fejer kernels give finite Fourier identities and collision bounds.",
        H("Signed-Mode Fejer Near-Collision Bounds"),
        Blocks(
            Paragraph(Text(
                "All quotients displayed with M occur in the real numbers after coercing M. "
                    + "The symbol g denotes the same finite real family in every binder and body.")),
            Describe.Lean(
                DescribeId.Create("signed-mode-fejer-kernel-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "fejerKernel"),
                H("The kernel is the signed integer-mode cosine sum"),
                StatementSource.FromAuthor(FejerDefinitionFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Zeros/fejer1903untersuchungen")),
                Blocks(Paragraph(Text(
                    "For natural M and real t, F_M(t) is the sum over every integer k with "
                        + "|k| < M of (1-|k|/M) cos(kt). This is the defining expression, "
                        + "not an abbreviation for a paired nonnegative-mode polynomial."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-fejer-energy-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "fejerEnergy"),
                H("Energy is the ordered double kernel sum"),
                StatementSource.FromAuthor(EnergyDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For g : Fin n -> R, fejerEnergy M g is the ordered sum of F_M(g_i-g_j) "
                        + "over all i and j in Fin n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-near-pair-count-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "nearPairCount"),
                H("Near-pair count is a filtered ordered-pair cardinality"),
                StatementSource.FromAuthor(NearCountDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "nearPairCount M g is the natural-number cardinality of ordered pairs (i,j) in "
                        + "Fin n squared whose values differ by at most pi/M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-fejer-square"),
                DeclarationHandle.Create(DeclarationPrefix + "fejer_square"),
                H("The signed-mode kernel is a normalized square"),
                StatementSource.FromAuthor(FejerSquareFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Zeros/fejer1903untersuchungen")),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural M and real t, the atom-defined signed-mode "
                            + "kernel equals one over M times the squared norm of the length-M "
                            + "geometric exponential sum.")),
                    Paragraph(Text(
                        "A private pairing lemma partitions the signed modes into zero, positive, "
                            + "and negative parts. The square identity is then proved by induction "
                            + "on the geometric-sum length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-fejer-energy-identity"),
                DeclarationHandle.Create(DeclarationPrefix + "fejer_energy_identity"),
                H("Ordered kernel energy equals signed Fourier energy"),
                StatementSource.FromAuthor(FejerEnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ordered double sum of the atom-defined kernel equals the signed "
                            + "mode sum of weighted squared exponential-sum norms. The proof swaps "
                            + "the finite sums and turns each cosine pair sum into a complex norm square.")),
                    Paragraph(Text(
                        "Named companion: fejer_energy_identity discharges the finite signed "
                            + "Fourier-energy identity obligation, atom 24.92 "
                            + "(ef059c215ec75472aa55d6d4b9c8fde6c5e8321ed941c9f51987d4402d8fa28f). "
                            + "preregistered named use: atom 24.92 obligation (评注 24.9x 预登记). "
                            + "The registration artifact is the candidate theorem 24.92 and remark "
                            + "27.799 in the PZG reference source. No public theorem in this module "
                            + "consumes fejer_energy_identity in its proof graph."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fejer-local-explicit-lower-bound"),
                DeclarationHandle.Create(DeclarationPrefix + "fejer_local_lower_bound"),
                H("The signed-mode kernel is large on its central window"),
                StatementSource.FromAuthor(FejerLocalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If M is positive and |t| <= pi/M, the atom-defined signed-mode kernel "
                        + "is at least 4M/pi^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-near-pair-count-bound"),
                DeclarationHandle.Create(DeclarationPrefix + "near_pair_count_bound"),
                H("Signed-mode energy controls ordered near collisions"),
                StatementSource.FromAuthor(NearPairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real coercion of the filtered ordered-pair cardinality is bounded by "
                        + "pi^2/(4M) times the displayed ordered double kernel sum. The proof "
                        + "uses the local lower bound on near pairs and square nonnegativity elsewhere."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-multiplicity-energy-lower-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "distinct_multiplicity_energy_lower_bound"),
                H("Signed-mode energy dominates squared multiplicities"),
                StatementSource.FromAuthor(MultiplicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed ordered double kernel sum is at least M times the sum, "
                            + "over values attained by g, of the squared real-coerced fiber cardinality.")),
                    Paragraph(Text(
                        "This finite inequality supplies no zeta-zero asymptotic and no positive "
                            + "proportion of simple zeros without an independent energy upper bound."))),
                DescribeRole.Theorem)),
        []));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula domain) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula NormSquare(Formula value) =>
        Power(new Formula.Norm(value), D(2));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Coerce(Formula value, Formula targetDomain) =>
        new Formula.Subscript(Call("val", value), targetDomain);

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula FamilyDomain(Formula n) =>
        new Formula.TypeArrow(Fin(n), Reals());

    private static Formula FamilyVariable() => F.Id(FamilyIdentifier);

    private static Formula GammaAt(Formula index) =>
        new Formula.Subscript(FamilyVariable(), index);

    private static Formula FejerSymbol(Formula m, Formula t) =>
        Apply(new Formula.Subscript(F.Id("F"), m), t);

    private static Formula EnergySymbol(Formula m) =>
        Call("fejerEnergy", m, FamilyVariable());

    private static Formula NearCountSymbol(Formula m) =>
        Call("nearPairCount", m, FamilyVariable());

    private static Formula IndexedSum(Formula condition, Formula body) =>
        Seq(new Formula.Subscript(Sum, condition), Sp, body);

    private static Formula SignedKernelBody(Formula m, Formula t)
    {
        Formula k = F.Id("k");
        Formula condition = And(Member(k, Integers()), Less(Absolute(k), Coerce(m, Integers())));
        Formula weight = Subtract(D(1), Divide(Coerce(Absolute(k), Reals()), Coerce(m, Reals())));
        Formula cosine = Call("cos", Multiply(Coerce(k, Reals()), t));
        return IndexedSum(condition, Multiply(Parenthesized(weight), cosine));
    }

    private static Formula PairEnergyBody(Formula n, Formula m)
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula difference = Subtract(GammaAt(i), GammaAt(j));
        return IndexedSum(Member(i, Fin(n)),
            IndexedSum(Member(j, Fin(n)),
                Parenthesized(SignedKernelBody(m, difference))));
    }

    private static Formula OrderedPairSet(Formula n, Formula m)
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula pair = Parenthesized(Seq(i, Comma, Sp, j));
        Formula pairDomain = Power(Fin(n), D(2));
        Formula difference = Absolute(Subtract(GammaAt(i), GammaAt(j)));
        Formula condition = LessEqual(difference, Divide(Pi, Coerce(m, Reals())));
        return Seq(Left, OpenBrace, pair, Sp, InMacro, Sp, pairDomain,
            Sp, Mid, Sp, condition, Right, CloseBrace);
    }

    private static Formula Cardinality(Formula set) => Seq(Lvert, set, Rvert);

    private static Formula RealCardinality(Formula set) =>
        Coerce(Cardinality(set), Reals());

    private static Formula FiberCardinality(Formula n, Formula value)
    {
        Formula i = F.Id("i");
        Formula fiber = Seq(Left, OpenBrace, i, Sp, InMacro, Sp, Fin(n),
            Sp, Mid, Sp, Equal(GammaAt(i), value), Right, CloseBrace);
        return RealCardinality(fiber);
    }

    private static Formula SignedFourierEnergy(Formula n, Formula m)
    {
        Formula k = F.Id("k");
        Formula i = F.Id("i");
        Formula modeCondition = And(Member(k, Integers()), Less(Absolute(k), Coerce(m, Integers())));
        Formula weight = Parenthesized(Subtract(D(1),
            Divide(Coerce(Absolute(k), Reals()), Coerce(m, Reals()))));
        Formula imaginaryUnit = new Formula.NamedConstant(FormulaIdentifier.Create("i"));
        Formula phase = Call("exp", Multiply(
            Coerce(Multiply(Coerce(k, Reals()), GammaAt(i)), Complexes()), imaginaryUnit));
        Formula phaseSum = IndexedSum(Member(i, Fin(n)), phase);
        return IndexedSum(modeCondition, Multiply(weight, NormSquare(phaseSum)));
    }

    private static Formula FejerDefinitionFormula()
    {
        Formula m = F.Id("M");
        Formula t = F.Id("t");
        return Disp(ForAll(
            [Bound("M", Naturals()), Bound("t", Reals())],
            Equal(FejerSymbol(m, t), SignedKernelBody(m, t))));
    }

    private static Formula EnergyDefinitionFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound(FamilyIdentifier, FamilyDomain(n))],
            Equal(EnergySymbol(m), PairEnergyBody(n, m))));
    }

    private static Formula NearCountDefinitionFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound(FamilyIdentifier, FamilyDomain(n))],
            Equal(NearCountSymbol(m), Cardinality(OrderedPairSet(n, m)))));
    }

    private static Formula FejerSquareFormula()
    {
        Formula m = F.Id("M");
        Formula t = F.Id("t");
        Formula r = F.Id("r");
        Formula imaginaryUnit = new Formula.NamedConstant(FormulaIdentifier.Create("i"));
        Formula range = And(LessEqual(D(0), r), Less(r, m));
        Formula phase = Call("exp", Multiply(
            Coerce(Multiply(Coerce(r, Reals()), t), Complexes()), imaginaryUnit));
        Formula exponentialSum = IndexedSum(range, phase);
        Formula square = Equal(
            SignedKernelBody(m, t),
            Multiply(Divide(D(1), Coerce(m, Reals())), NormSquare(exponentialSum)));
        return Disp(ForAll(
            [Bound("M", Naturals()), Bound("t", Reals())],
            Implies(LessEqual(D(1), m), square)));
    }

    private static Formula FejerEnergyFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        Formula identity = Equal(PairEnergyBody(n, m), SignedFourierEnergy(n, m));
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound(FamilyIdentifier, FamilyDomain(n))],
            identity));
    }

    private static Formula FejerLocalFormula()
    {
        Formula m = F.Id("M");
        Formula t = F.Id("t");
        Formula premise = And(
            LessEqual(D(1), m), LessEqual(Absolute(t), Divide(Pi, Coerce(m, Reals()))));
        Formula lowerBound = LessEqual(
            Divide(Multiply(D(4), Coerce(m, Reals())), Power(Pi, D(2))), SignedKernelBody(m, t));
        return Disp(ForAll(
            [Bound("M", Naturals()), Bound("t", Reals())],
            Implies(premise, lowerBound)));
    }

    private static Formula NearPairFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        Formula coefficient = Divide(Power(Pi, D(2)), Multiply(D(4), Coerce(m, Reals())));
        Formula conclusion = LessEqual(
            RealCardinality(OrderedPairSet(n, m)),
            Multiply(coefficient, PairEnergyBody(n, m)));
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound(FamilyIdentifier, FamilyDomain(n))],
            Implies(LessEqual(D(1), m), conclusion)));
    }

    private static Formula MultiplicityFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("M");
        Formula v = F.Id("v");
        Formula imageCondition = Member(v, Call("im", FamilyVariable()));
        Formula mass = IndexedSum(
            imageCondition, Power(FiberCardinality(n, v), D(2)));
        Formula conclusion = LessEqual(
            Multiply(Coerce(m, Reals()), mass), PairEnergyBody(n, m));
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("M", Naturals()),
                Bound(FamilyIdentifier, FamilyDomain(n))],
            Implies(LessEqual(D(1), m), conclusion)));
    }
}
