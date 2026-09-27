using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class PrimePowerNonadaptiveResolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime and positive depth, fixed capped valuation queries identify a "
            + "residue exactly when their centers omit at most one leaf from each final "
            + "sibling fiber. The minimum number of actual calls is attained.",
        H("Prime-power Nonadaptive Resolution"),
        Blocks(
            Paragraph(Text(
                "Fix a prime p and a natural e at least one. Write X for ZMod of p to "
                    + "the power e, Y for ZMod of p to the power e minus one, and K for "
                    + "the product of p minus one with p to the power e minus one. "
                    + "The map rho at depth d is the canonical reduction from X to "
                    + "ZMod of p to the power d; pi is rho at depth e minus one. "
                    + "The symbols h and q below abbreviate depth and query at the fixed p and e. "
                    + "Write r for PadicInt.toZModPow at depth e and P for the p-adic integers.")),
            Describe.Lean(
                DescribeId.Create("congruence-depth"),
                DeclarationHandle.Create(Prefix + "depth"),
                H("The maximum congruence depth"),
                StatementSource.FromAuthor(DepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite maximum includes depth zero, where the modulus is one. "
                        + "The supremum is implemented on a filtered finite range."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-aware-query"),
                DeclarationHandle.Create(Prefix + "query"),
                H("A capped valuation query at a natural center"),
                StatementSource.FromAuthor(QueryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conditional returns e when x plus n is zero. Otherwise it returns "
                        + "the smaller of e and the p-adic valuation. Thus the zero input "
                        + "has the cap value, as required for an extended valuation."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "For a finite center set S, H(S) is jointReadout of the family sending a "
                    + "center c in S to h(c, a). The notation O(S, y) denotes the finite "
                    + "set of a in the complement of S with pi(a) equal to y. Its "
                    + "cardinality counts omitted leaves in that fiber. For n indexed by "
                    + "Fin(k), Q(n) is jointReadout of the actual functions q(n(i), x). "
                    + "FactorsThrough(r, Q(n)) says that equal full query signatures "
                    + "imply equal target residues for every pair of p-adic states. "
                    + "It imposes no distinctness condition on n; all k calls are charged.")),
            Describe.Lean(
                DescribeId.Create("resolving-criterion-and-attained-minimum"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The resolving criterion and the attained call minimum"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reduction compatibility gives the threshold characterization of h. "
                            + "The kernel of p-adic reduction identifies its zero test with "
                            + "the valuation threshold, including the separate zero case. "
                            + "Consequently the target leaf is minus r(x) and the center is "
                            + "the natural number n reduced in X. Every target leaf is "
                            + "realized by the negative of its natural representative.")),
                    Paragraph(Text(
                        "The final reduction is a surjective additive homomorphism, so its "
                            + "fibers have equal cardinalities. Summing them gives p leaves "
                            + "per fiber. Two omitted siblings have the same reply at every "
                            + "selected center. Conversely a selected endpoint separates a "
                            + "same-fiber pair; for different fibers a selected center in "
                            + "the first fiber separates them. Such a center exists because "
                            + "the fiber has p leaves and at most one is omitted.")),
                    Paragraph(Text(
                        "The final reduction is injective on the omitted set, bounding its "
                            + "cardinality by the cardinality of Y. To attain the resulting "
                            + "lower bound, omit the canonical natural representative of "
                            + "each element of Y and query every other leaf. Enumerating "
                            + "that finite set and using natural representatives supplies "
                            + "an actual query list. For any list, its image has cardinality "
                            + "at most its length and gives exactly the same distinctions. "
                            + "Repeated centers therefore cannot improve the minimum. "
                            + "The argument includes e equal to one and p equal to two."))),
                DescribeRole.Theorem))));

    private static Formula P => F.Id("p");
    private static Formula E => F.Id("e");
    private static Formula A => F.Id("a");
    private static Formula C => F.Id("c");
    private static Formula Dp => F.Id("d");
    private static Formula X => F.Id("X");
    private static Formula Y => F.Id("Y");
    private static Formula S => F.Id("S");
    private static Formula N => F.Id("n");
    private static Formula State => F.Id("x");
    private static Formula K => F.Id("K");
    private static Formula Count => F.Id("k");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Hdepth => Call("h", C, A);
    private static Formula Rho(Formula a) => Call("rho", Dp, a);
    private static Formula Residue(Formula a) => Call("r", a);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Omitted(Formula y) => Call("O", S, y);
    private static Formula Resolves => Call("Injective", Call("H", S));
    private static Formula PairQuantifier => Seq(Forall, Sp, C, Comma, A, Sp, InMacro, Sp, X, Comma, Sp);
    private static Formula Bracket(Formula f) => Seq(Open, f, Close);

    private static Formula DepthFormula() => Disp(Seq(
        PairQuantifier, Hdepth, Sp, Eq, Sp, Call("max", Seq(
            OpenBrace, Dp, Sp, InMacro, Sp, Naturals, Sp, Mid, Sp,
            D(0), Sp, Leq, Sp, Dp, Sp, Leq, Sp, E, Sp, Land, Sp,
            Rho(A), Sp, Eq, Sp, Rho(C), CloseBrace)), Dot));

    private static Formula QueryFormula() => Disp(Seq(
        Forall, Sp, State, Sp, InMacro, Sp, F.Id("P"), Comma, Sp,
        N, Sp, InMacro, Sp, Naturals, Comma, Sp,
        Call("q", N, State), Sp, Eq, Sp, Call("ite",
            Seq(State, Sp, Plus, Sp, N, Sp, Eq, Sp, D(0)), E,
            Call("min", E, Call("valuation", Seq(State, Sp, Plus, Sp, N)))), Dot));

    private static Formula ResultFormula()
    {
        Formula y = F.Id("y");
        Formula bounded = Seq(PairQuantifier, Hdepth, Sp, Leq, Sp, E, Sp, Land, Sp,
            Bracket(Seq(Forall, Sp, Dp, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Dp, Sp, Leq, Sp, E, Sp, Rightarrow, Sp,
                Bracket(Seq(Dp, Sp, Leq, Sp, Hdepth, Sp, Iff, Sp,
                    Rho(A), Sp, Eq, Sp, Rho(C))))));
        Formula diagonal = Seq(PairQuantifier,
            Bracket(Seq(Hdepth, Sp, Eq, Sp, E, Sp, Iff, Sp, A, Sp, Eq, Sp, C)));
        Formula bridge = Seq(Forall, Sp, State, Sp, InMacro, Sp, F.Id("P"), Comma, Sp,
            N, Sp, InMacro, Sp, Naturals, Comma, Sp, Call("q", N, State), Sp, Eq, Sp,
            Call("h", Call("cast", N), Seq(Minus, Residue(State))));
        Formula realized = Call("Surjective", Seq(State, Sp, Mapsto, Sp, Minus, Residue(State)));
        Formula centers = Seq(Forall, Sp, C, Sp, InMacro, Sp, X, Comma, Sp,
            Exists, Sp, N, Sp, InMacro, Sp, Naturals, Comma, Sp,
            N, Sp, Lt, Sp, new Formula.Power(P, E), Sp, Land, Sp, Call("cast", N), Sp, Eq, Sp, C);
        Formula fiberCount = Seq(Card(Y), Sp, Eq, Sp,
            new Formula.Power(P, Seq(E, Sp, Minus, Sp, D(1))));
        Formula fiberSize = Seq(Forall, Sp, y, Sp, InMacro, Sp, Y, Comma, Sp,
            Card(Seq(OpenBrace, A, Sp, InMacro, Sp, X, Sp, Mid, Sp,
                Call("pi", A), Sp, Eq, Sp, y, CloseBrace)), Sp, Eq, Sp, P);
        Formula criterion = Seq(Forall, Sp, S, Colon, Sp, Call("Finset", X), Comma, Sp,
            Bracket(Seq(Resolves, Sp, Iff, Sp,
                Bracket(Seq(Forall, Sp, y, Sp, InMacro, Sp, Y, Comma, Sp,
                    Card(Omitted(y)), Sp, Leq, Sp, D(1))))));
        Formula attaining = Seq(Exists, Sp, S, Colon, Sp, Call("Finset", X), Comma, Sp,
            Card(S), Sp, Eq, Sp, K, Sp, Land, Sp,
            Bracket(Seq(Forall, Sp, y, Sp, InMacro, Sp, Y, Comma, Sp,
                Card(Omitted(y)), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Resolves);
        Formula feasible = Seq(OpenBrace, Count, Sp, InMacro, Sp, Naturals, Sp, Mid, Sp,
            Exists, Sp, N, Colon, Sp, Call("Fin", Count), Sp, To, Sp, Naturals, Comma, Sp,
            Call("FactorsThrough", F.Id("r"), Call("Q", N)), CloseBrace);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, P, Comma, E, Sp, InMacro, Sp, Naturals, Comma, Sp,
                Call("Prime", P), Sp, Land, Sp, D(1), Sp, Leq, Sp, E, Sp, Rightarrow),
            Seq(Bracket(bounded), Sp, Land),
            Seq(Bracket(diagonal), Sp, Land),
            Seq(Bracket(bridge), Sp, Land),
            Seq(Bracket(realized), Sp, Land),
            Seq(Bracket(centers), Sp, Land),
            Seq(Bracket(fiberCount), Sp, Land),
            Seq(Bracket(fiberSize), Sp, Land),
            Seq(Bracket(criterion), Sp, Land),
            Seq(Bracket(attaining), Sp, Land),
            Seq(Call("IsLeast", feasible, K), Dot)
        ]));
    }
}
