using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors;

internal sealed class FiniteRankBoundaryDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive harmonic pairs have rank at most four thirds; three pairs can approach two, "
            + "and every finite injective paired family has rank strictly below two.",
        H("Finite Paired Harmonic Rank Boundary"),
        Blocks(
            Paragraph(Text(
                "Let I be a finite nonempty index set, k an injective map from I to positive "
                    + "natural frequencies, and a a positive real amplitude at every index. "
                    + "The physical state is x(phi)=(cos(phi),sin(phi)). The sensor H(phi) "
                    + "has coordinate pair a(i)(cos(k(i)phi),sin(k(i)phi)) for each i. "
                    + "Physical injectivity means that equality of sensor outputs implies "
                    + "equality of x(phi) and x(psi). PhysicalFamily(I,k,a) denotes exactly "
                    + "these assumptions, including physical injectivity.")),
            Paragraph(Text(
                "Set theta=pi/6. The delay matrix X(phi) has rows H(phi) and H(phi-theta). "
                    + "R(k,a) is the infimum, over all x(phi) unequal to x(psi), of the "
                    + "squared Frobenius norm of X(phi)-X(psi) divided by its squared "
                    + "Euclidean operator norm. No phase interval is removed from this infimum. "
                    + "For d=phi-psi, write A(d)=4 sum_i a(i)^2 sin(k(i)d/2)^2 and "
                    + "B(d)=4 sum_i a(i)^2 cos(k(i)theta) sin(k(i)d/2)^2. The row Gram "
                    + "matrix has diagonal A and off-diagonal B. Its actual norm formulas "
                    + "give the chord rank 2/(1+abs(B)/A), and injectivity gives A>0.")),
            Describe.Lean(
                DescribeId.Create("at-most-two-pairs"),
                DeclarationHandle.Create(Owner + "at_most_two_pairs"),
                H("The complete one-or-two-pair upper bound"),
                StatementSource.FromAuthor(SmallFamilyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a single frequency, the physical kernel theorem forces frequency one. "
                            + "Every nonzero chord then has B/A=cos(pi/6), whose absolute value "
                            + "exceeds one half.")),
                    Paragraph(Text(
                        "For distinct frequencies m and n, injectivity gives gcd(m,n)=1. "
                            + "When n>1, the chord d=2pi/n is a pair of distinct physical states. "
                            + "The n-th difference vanishes. The remaining energy is positive "
                            + "by injectivity, so B/A=cos(m pi/6) on this chord. If both "
                            + "frequencies exceed one, both endpoints are available and the "
                            + "coprime cosine obstruction supplies one with magnitude at least "
                            + "one half. If one frequency is one, isolate that frequency by "
                            + "killing the other. The physical infimum is therefore at most "
                            + "four thirds in all cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-three-attainment-and-normalization"),
                DeclarationHandle.Create(Owner + "two_three_attainment_and_normalization"),
                H("Sharp attainment and unit derivative"),
                StatementSource.FromAuthor(AttainmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In this formula k23=(2,3), PositiveAmplitudes2 consists of arbitrary "
                            + "positive real pairs, RealAmplitudeMaps(Fin2) consists of all real "
                            + "amplitude maps on Fin2={0,1}, and component(a,i)=a(i). "
                            + "The existential witness b satisfies, for every i in Fin2, "
                            + "b(i)=a(i)/sqrt(4a(0)^2+9a(1)^2), exactly as in the Lean conclusion. "
                            + "Both the original and normalized sensors are physically injective. "
                            + "At frequencies two and three the two cosine coefficients are "
                            + "one half and zero. Nonnegativity of the two harmonic energies gives abs(B)<=A/2 "
                            + "on every physical chord. Together with the upper bound this gives "
                            + "R=4/3 for every positive amplitude pair.")),
                    Paragraph(Text(
                        "The derivative of each planar pair has squared norm k(i)^2 a(i)^2. "
                            + "The pairs occupy orthogonal coordinates, so the squared norm of "
                            + "the full derivative is 4a(0)^2+9a(1)^2. Dividing the amplitudes "
                            + "by the positive square root of this quantity gives derivative norm "
                            + "one at every phase. The arbitrary-amplitude result gives rank "
                            + "four thirds for this normalized sensor as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-rank-strict"),
                DeclarationHandle.Create(Owner + "finite_rank_strict"),
                H("Strict nonattainment for every finite positive family"),
                StatementSource.FromAuthor(StrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose R>=2. Each physical chord has positive energy, and the actual "
                            + "norm formula then forces B(d)=0 on every distinct-state chord. "
                            + "When x(d)=x(0), d is an integer multiple of 2pi, so all harmonic "
                            + "sine differences vanish and B(d)=0 there also.")),
                    Paragraph(Text(
                        "Write w(i)=a(i)^2 and c(i)=cos(k(i)theta). The half-angle identity "
                            + "now gives sum_i w(i)c(i)=sum_i w(i)c(i)cos(k(i)d) for every d. "
                            + "Integrating over a full period makes the right side zero, since "
                            + "each frequency is a positive integer. Evaluating the same identity "
                            + "at d=theta gives sum_i w(i)c(i)^2=0. Each w(i)>0, so every c(i)=0.")),
                    Paragraph(Text(
                        "At d=2pi/3=4theta, the half-chord sine is "
                            + "sin(2k(i)theta)=2sin(k(i)theta)cos(k(i)theta)=0. Thus A(d)=0. "
                            + "This is a distinct physical third-turn chord, contradicting "
                            + "injectivity. Hence R<2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-pair-count"),
                DeclarationHandle.Create(Owner + "minimum_pair_count"),
                H("Exactly three pairs are necessary and sufficient to approach two"),
                StatementSource.FromAuthor(Disp(And(
                    Call("IsLeast", F.Id("ApproachingPairCounts"), Num(3)),
                    Equal(Call("realDimension", Call("EuclideanPairedSpace", Num(3))), Num(6))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "EuclideanPairedSpace(n) is the real Euclidean space indexed by Fin n times Fin 2. "
                            + "ApproachingPairCounts is the set of natural numbers n such that "
                            + "for every real r<2 there exist positive amplitudes and distinct "
                            + "positive frequencies indexed by Fin n, with physically injective "
                            + "sensor and R>r. The empty family is not injective. The one- and "
                            + "two-pair bound excludes both smaller positive counts, for example "
                            + "by taking r=3/2.")),
                    Paragraph(Text(
                        "For sufficiency use the actual six-coordinate family with frequencies "
                            + "(2,3,4), amplitudes (sqrt(epsilon),1,sqrt(epsilon))/sqrt(9+20epsilon), "
                            + "and 0<epsilon<=1/2. Its gcd is one and all amplitudes are positive. "
                            + "The physical rank-defect limit "
                            + "(2-R)/sqrt(epsilon/2) -> 1 implies R -> 2 from positive epsilon. "
                            + "Consequently these three-pair sensors satisfy every threshold r<2. "
                            + "The strict finite-family result shows that no such sensor, nor any "
                            + "other finite sensor in this class, reaches two exactly."))),
                DescribeRole.Theorem),
            Paragraph(
                Text("The sensor-design question in "),
                Ref("D5/L/ConceptDynamics/eftekhari2018embedology"),
                Text(" motivates the stable-rank comparison. The pair count here concerns the "
                    + "specified positive harmonic pairs at two fixed delays. It is not a "
                    + "minimum-dimension theorem for arbitrary smooth sensors or arbitrary "
                    + "delay schemes.")))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Rank(Formula k, Formula a) => Call("R", k, a);
    private static Formula Ratio => new Formula.Fraction(Num(4), Num(3));
    private static Formula FamilyFormula(Formula conclusion)
    {
        Formula i = F.Id("I"), k = F.Id("k"), a = F.Id("a");
        return Disp(All([Bound("I", F.Id("FiniteNonemptyTypes")),
                Bound("k", Call("NaturalFrequencyMaps", i)),
                Bound("a", Call("RealAmplitudeMaps", i))],
            Implies(Call("PhysicalFamily", i, k, a), conclusion)));
    }
    private static Formula SmallFamilyFormula() => FamilyFormula(
        Implies(Le(Call("card", F.Id("I")), Num(2)), Le(Rank(F.Id("k"), F.Id("a")), Ratio)));
    private static Formula StrictFormula() => FamilyFormula(
        new Formula.Relation(Rank(F.Id("k"), F.Id("a")), FormulaRelationOperator.LessThan, Num(2)));
    private static Formula AttainmentFormula()
    {
        Formula a = F.Id("a"), k = F.Id("k23"), b = F.Id("b"), i = F.Id("i");
        Formula budget = new Formula.Binary(
            new Formula.Binary(Num(4), FormulaBinaryOperator.Multiply,
                new Formula.Power(Call("component", a, Num(0)), Num(2))),
            FormulaBinaryOperator.Add,
            new Formula.Binary(Num(9), FormulaBinaryOperator.Multiply,
                new Formula.Power(Call("component", a, Num(1)), Num(2))));
        Formula normalization = All([Bound("i", F.Id("Fin2"))],
            Equal(Call("component", b, i),
                new Formula.Fraction(Call("component", a, i), Call("sqrt", budget))));
        Formula normalizedConclusions = And(normalization,
            And(Call("PositiveAmplitudes2", b),
                And(Call("PhysicallyInjective", k, b),
                    And(Equal(Rank(k, b), Ratio),
                        All([Bound("phi", F.Id("Real"))],
                            Equal(Call("derivativeNorm", k, b, F.Id("phi")), Num(1)))))));
        Formula witness = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("b", Call("RealAmplitudeMaps", F.Id("Fin2")))], normalizedConclusions);
        return Disp(All([Bound("a", F.Id("PositiveAmplitudes2"))],
            And(Call("PhysicallyInjective", k, a), And(Equal(Rank(k, a), Ratio), witness))));
    }
}
