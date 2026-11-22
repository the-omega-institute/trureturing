using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class WeightedPhaseRelationLatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete integer relation lattice gives uniform lower and upper bounds for the "
        + "weighted sine deficit at a common real time.",
        H("Weighted Phase Deficit and the Complete Relation Lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-phase-orbit-closure"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit"),
                H("Continuous orbit closure"),
                StatementSource.FromAuthor(OrbitFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Fourier/onishchik2020kronecker")),
                Blocks(Paragraph(Text(
                    "For each nonzero integer dot product with the frequency vector, the "
                    + "steps that turn it into an integral multiple of 2π form a countable set. "
                    + "One step in (0,1) avoids their union. Its discrete characters are exactly "
                    + "the zero-dot-product characters, so TorusOrbitClosure.result puts every "
                    + "point in their common kernel in the real orbit closure. The forward "
                    + "inclusion follows from character continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered-phase-lift"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRelationLattice.centered_lift_iff"),
                H("Centered angles and integer congruences"),
                StatementSource.FromAuthor(LiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here R is the entrywise real cast of the integer row matrix K. Testing "
                    + "each row gives an integer winding number for the angle x + (π/2)1. "
                    + "Each integer relation uses only finitely many rows, even for an "
                    + "arbitrary row index type A. The same finite integral combination "
                    + "of their winding numbers gives the winding for that relation, so "
                    + "the row congruences imply every character equation. Every point of "
                    + "the closure has a lift of this form with x in (−π,π] coordinatewise. "
                    + "Rotate by −π/2 and take the argument on the unit circle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-gram-inverse-deficit"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRelationLattice.weighted_phase_deficit_bounds"),
                H("Uniform inverse Gram energy comparison"),
                StatementSource.FromAuthor(BoundsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite J gives finite character products and weighted sums. "
                        + "With finite A the Gram matrix admits the usual finite matrix inverse "
                        + "once positive definiteness is established. Positive individual weights "
                        + "make M and M⁻¹ positive definite. "
                        + "Real independence of the cast rows makes Rᵀ injective, so its "
                        + "pullback G = R M⁻¹ Rᵀ is positive definite and invertible. For "
                        + "each z, the vector x₀ = M⁻¹RᵀG⁻¹b(z) satisfies Rx₀ = b(z). Its squared M-norm is "
                        + "b(z)ᵀG⁻¹b(z). The M-cross term vanishes for each displacement in "
                        + "the kernel of R, so this is the attained minimum for that fiber.")),
                    Paragraph(Text(
                        "Positive total weight W permits normalization and preserves the "
                        + "inequality directions when dividing by W. Full integral row generation "
                        + "ensures that the affine fibers enforce every character equation of the "
                        + "orbit closure. A proper sublattice can admit extra lifts and lower E.")),
                    Paragraph(Text(
                        "Two hand-checked examples illustrate these hypotheses. When J is empty, "
                        + "the sum and W are zero. Totalized division gives score zero and D = 1, "
                        + "while E/(2W) is zero. For one frequency γ = 0 with weight 1, the full "
                        + "relation lattice is ℤ. The single row K = [4] generates 4ℤ, and z = 1 "
                        + "gives b(z) = 0. Since G = [16], each winding energy is a square "
                        + "divided by 16, so E = 0. The sine score is always zero, so D = 1 "
                        + "and the upper bound fails.")),
                    Paragraph(Text(
                        "The continuous weighted sine deficit on the orbit closure has the "
                        + "same infimum as along the real-time orbit. In principal centered "
                        + "angles, the pointwise lower estimate for 1 − cos x has coefficient "
                        + "2/π² on x². The upper estimate has coefficient 1/2 for every real x "
                        + "and applies to the affine minimizers. Taking the infimum over all "
                        + "integer windings gives the bounds. Empty A gives zero inverse Gram "
                        + "energy and hence zero deficit.")),
                    Paragraph(Text(
                        "For the ζ-ordinate example, assume hRH proves Mathlib's "
                        + "RiemannHypothesis. Form zetaSpectrum hRH, then use the finite index "
                        + "type of members of Spectrum.cut (zetaSpectrum hRH) T, which keeps "
                        + "the positive ordinates γ with γ ≤ T. Multiply the chosen positive "
                        + "weight per occurrence by the analytic multiplicity of its zero. "
                        + "The comparison applies given a complete relation basis and positive "
                        + "total weight. Bounding the normalized energy for the actual ζ "
                        + "ordinates is a separate question."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integer => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Circle => Seq(Mathbb, Grp(F.Id("T")));
    private static Formula Vector(Formula field, string index) => new Formula.Power(field, F.Id(index));
    private static Formula Matrix(Formula field) => new Formula.Power(field, Seq(F.Id("A"), Times, Sp, F.Id("J")));
    private static Formula At(string name) => new Formula.Subscript(F.Id(name), F.Id("j"));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Diff(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula PlusOf(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula PiHalf => new Formula.Fraction(Pi, D(2));
    private static Formula Inv(Formula x) => new Formula.Power(x, new Formula.Negate(D(1)));
    private static Formula Tr(Formula x) => new Formula.Power(x, F.Id("T"));
    private static Formula SumJ(Formula x) => Seq(Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")), Sp, x);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Equivalence(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula AtMost(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Positive(Formula x) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, x);
    private static Formula.BoundVariable Var(string name, Formula domain) => new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula TorusPoint(Formula angle) =>
        new Formula.Sequence(Call("exp", Mul(F.Id("i"), angle)), F.Id("j"), F.Id("J"));

    private static Formula Orbit() =>
        Call("closure", new Formula.SetBuilder(TorusPoint(Mul(At("g"), F.Id("t"))), F.Id("t"), Real));

    private static Formula RelationDot() => Equal(SumJ(Mul(At("k"), At("g"))), D(0));

    private static Formula OrbitFormula()
    {
        var character = Seq(Prod, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")), Sp,
            new Formula.Power(At("p"), At("k")));
        var relations = All(Imp(RelationDot(), Equal(character, D(1))), Var("k", Vector(Integer, "J")));
        var points = Seq(OpenBrace, F.Id("p"), InMacro, Sp, Vector(Circle, "J"), Sp, Mid, Sp,
            relations, CloseBrace);
        return Disp(All(Equal(Orbit(), points), Var("J", F.Id("FiniteType")), Var("g", Vector(Real, "J"))));
    }

    private static Formula LatticeHypothesis() =>
        All(Equivalence(Member(F.Id("k"), Call("spanZ", Call("rows", F.Id("K")))), RelationDot()),
            Var("k", Vector(Integer, "J")));

    private static Formula CastEquality() => Equal(F.Id("R"), Call("cast", F.Id("K")));

    private static Formula Offset() =>
        Diff(Mul(Mul(D(2), Pi), F.Id("z")), Mul(PiHalf, Mul(F.Id("R"), Seq(Mathbf, Grp(D(1))))));

    private static Formula LiftFormula()
    {
        var winding = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("z"),
            Vector(Integer, "A"), Equal(Mul(F.Id("R"), F.Id("x")), Offset()));
        return Disp(All(
            Imp(And(CastEquality(), LatticeHypothesis()),
                Equivalence(Member(TorusPoint(PlusOf(At("x"), PiHalf)), Orbit()), winding)),
            Var("J", F.Id("FiniteType")), Var("A", F.Id("Type")), Var("g", Vector(Real, "J")),
            Var("K", Matrix(Integer)), Var("R", Matrix(Real)), Var("x", Vector(Real, "J"))));
    }

    private static Formula BoundsFormula()
    {
        var w = F.Id("W");
        var e = F.Id("E");
        var d = F.Id("D");
        var bz = Call("b", F.Id("z"));
        var score = new Formula.Fraction(SumJ(Mul(At("w"), Call("sin", Mul(At("g"), F.Id("t"))))), w);
        var infimum = Seq(Operatorname, Grp(F.Id("inf")), Underscore,
            Grp(F.Id("z"), InMacro, Sp, Vector(Integer, "A")), Sp, Mul(Mul(Tr(bz), Inv(F.Id("G"))), bz));
        var supremum = Seq(Operatorname, Grp(F.Id("sup")), Underscore, Grp(F.Id("t"), InMacro, Sp, Real),
            Sp, score);
        var hypothesis = And(All(Positive(At("w")), Var("j", F.Id("J"))), And(Positive(w),
            And(CastEquality(), And(LatticeHypothesis(),
                Call("LinearlyIndependent", Real, Call("rows", F.Id("R")))))));
        var weightSum = Equal(w, SumJ(At("w")));
        var diagonal = Equal(F.Id("M"), Call("diag", F.Id("w")));
        var gram = Equal(F.Id("G"), Mul(Mul(F.Id("R"), Inv(F.Id("M"))), Tr(F.Id("R"))));
        var offset = All(Equal(bz, Offset()), Var("z", Vector(Integer, "A")));
        var energyAndDeficit = And(Equal(e, infimum), Equal(d, Diff(D(1), supremum)));
        var definitions = And(weightSum, And(diagonal, And(gram, And(offset, energyAndDeficit))));
        var comparison = And(AtMost(new Formula.Fraction(Mul(D(2), e), Mul(new Formula.Power(Pi, D(2)), w)), d),
            And(AtMost(d, new Formula.Fraction(e, Mul(D(2), w))),
                Imp(Call("IsEmpty", F.Id("A")), Equal(e, D(0)))));
        return Disp(All(Imp(hypothesis, Imp(definitions, comparison)),
            Var("J", F.Id("FiniteType")), Var("A", F.Id("FiniteType")),
            Var("g", Vector(Real, "J")), Var("w", Vector(Real, "J")),
            Var("K", Matrix(Integer)), Var("R", Matrix(Real)),
            Var("W", Real), Var("M", new Formula.Power(Real, Seq(F.Id("J"), Times, Sp, F.Id("J")))),
            Var("G", new Formula.Power(Real, Seq(F.Id("A"), Times, Sp, F.Id("A")))),
            Var("b", new Formula.TypeArrow(Vector(Integer, "A"), Vector(Real, "A"))),
            Var("E", Real), Var("D", Real)));
    }
}
