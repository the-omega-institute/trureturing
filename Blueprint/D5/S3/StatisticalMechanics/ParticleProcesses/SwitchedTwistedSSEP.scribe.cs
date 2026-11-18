using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.ParticleProcesses;

internal sealed class SwitchedTwistedSSEPDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/dabrowski2026twistedssep");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating equilibrated twisted exclusion models have full support exactly under the derived-group or two-site pair-group criterion.",
        H("Switched twisted symmetric exclusion processes"),
        Blocks(
            Paragraph(Text("The source is Dabrowski, Poulain d’Andecy and Ragoucy, Sections 3.1, 4, 5.1 and 7. "
                + "Sites use zero-based Fin L indices; species use Fin N. The source assumes N positive and L at least two. "
                + "The formal statement also covers N zero, where configurations form an empty space. "
                + "The evolution is the equilibrated switching of Proposition 5.2: each model is run to its sector-uniform stationary distribution. "
                + "No finite-time relaxation rate is asserted.")),
            Definition("Configuration", All("L", Nat(), All("N", Nat(),
                Equal(Call("Configuration", X("L"), X("N")), Arrow(Fin(X("L")), Fin(X("N")))))),
                "A configuration assigns one species to each lattice site."),
            Definition("adjacentMove", LN(All("i", Fin(X("L")), All("hi", LT(Add(Val(X("i")), D(1)), X("L")),
                All("x", Config(), Equal(Call("adjacentMove", X("i"), X("hi"), X("x")),
                    Call("Function.comp", X("x"), Call("Equiv.swap", X("i"),
                        Typed(Add(Val(X("i")), D(1)), Fin(X("L")))))))))),
                "Exchange sites i and i plus one, with the explicit upper-bound proof hi."),
            Definition("lastSite", All("L", Nat(), All("hL", LT(D(1), X("L")),
                Equal(Typed(Call("lastSite", X("hL")), Fin(X("L"))),
                    Typed(Subtract(X("L"), D(1)), Fin(X("L")))))),
                "The final site has natural value L minus one; hL supplies its bound."),
            Definition("firstSite", All("L", Nat(), All("hL", LT(D(1), X("L")),
                Equal(Typed(Call("firstSite", X("hL")), Fin(X("L"))), Typed(D(0), Fin(X("L")))))),
                "The first site has natural value zero."),
            Definition("boundaryMove", Context(All("s", Perm(), All("x", Config(), All("i", Fin(X("L")),
                Equal(At(Call("boundaryMove", X("hL"), X("s"), X("x")), X("i")),
                    Ite(Equal(X("i"), First()), At(Inv(X("s")), At(X("x"), Last())),
                        Ite(Equal(X("i"), Last()), At(X("s"), At(X("x"), First())), At(X("x"), X("i"))))))))),
                "At the first site take the inverse twist of the last entry; at the last site take the twist of the first entry. Other sites retain their entries. This is equation 3.3."),
            Definition("moveRelation", Context(All("s", Perm(), XY(IffF(Call("moveRelation", X("hL"), X("s"), X("x"), X("y")),
                OrF(Some("i", Fin(X("L")), Some("hi", LT(Add(Val(X("i")), D(1)), X("L")),
                    Equal(X("y"), Call("adjacentMove", X("i"), X("hi"), X("x"))))),
                    Equal(X("y"), Call("boundaryMove", X("hL"), X("s"), X("x")))))))),
                "An elementary move is either one allowed adjacent exchange or the twisted boundary exchange. Every elementary move is an involution."),
            Definition("sector", Context(All("s", Perm(), All("x", Config(),
                Equal(Call("sector", X("hL"), X("s"), X("x")),
                    Call("Finset.filter", Lam("y", Config(),
                        Call("Relation.EqvGen", Call("moveRelation", X("hL"), X("s")), X("x"), X("y"))),
                        Typed(Q("Finset", "univ"), Finset(Config()))))))),
                "A sector is the finite set of configurations in the equivalence closure of the elementary moves. It contains its representative."),
            Definition("branchingProbability", Context(ST(XY(Equal(
                Typed(Call("branchingProbability", X("hL"), X("s"), X("t"), X("x"), X("y")), Rat()),
                new Formula.Fraction(Typed(Card(Inter(Sector("s", "x"), Sector("t", "y"))), Rat()),
                    Typed(Card(Sector("s", "x")), Rat())))))),
                "Proposition 5.2 assigns the intersection cardinality divided by the initial sector cardinality. The denominator is strictly positive because the initial representative belongs to its sector."),
            Definition("overlap", Context(ST(XY(IffF(
                Call("overlap", X("hL"), X("s"), X("t"), X("x"), X("y")),
                Call("Finset.Nonempty", Inter(Sector("s", "x"), Sector("t", "y"))))))),
                "The two sectors overlap exactly when their intersection contains a configuration."),
            Definition("unionMoveRelation", Context(FG(XY(IffF(UnionMove(), OrF(
                Call("moveRelation", X("hL"), X("f"), X("x"), X("y")),
                Call("moveRelation", X("hL"), X("g"), X("x"), X("y"))))))),
                "The union graph allows an elementary move of either twist."),
            Definition("unionConnected", Context(FG(IffF(Call("unionConnected", X("hL"), X("f"), X("g")),
                XY(Call("Relation.EqvGen", Call("unionMoveRelation", X("hL"), X("f"), X("g")), X("x"), X("y")))))),
                "Connected means that every ordered pair of configurations belongs to the union relation's equivalence closure."),
            Definition("sectorsOf", Context(All("s", Perm(), All("C", Finset(Config()), IffF(
                Member(X("C"), Call("sectorsOf", X("hL"), X("s"))),
                Some("x", Config(), Equal(X("C"), Sector("s", "x"))))))),
                "The sector family consists exactly of sectors obtained from a representative configuration."),
            Definition("alternatingSectorReach", Context(FG(StartC(AndF(
                All("D", Finset(Config()), IffF(Member(X("D"), Reach(D(0))), Equal(X("D"), X("C")))),
                All("k", Nat(), All("D", Finset(Config()), IffF(Member(X("D"), Reach(Add(X("k"), D(1)))),
                    AndF(Member(X("D"), Call("sectorsOf", X("hL"), NextTwist())),
                        Some("E", Finset(Config()), AndF(Member(X("E"), Reach(X("k"))),
                            Call("Finset.Nonempty", Inter(X("E"), X("D"))))))))))))),
                "At zero steps the reached sector set is the singleton initial set C. At step k plus one use g when start equals the Boolean test that k is even, and f otherwise. Keep precisely sectors intersecting a previously reached set. This formula also defines the operation for arbitrary finite initial C."),
            Definition("switchSupport", Context(FG(StartC(All("k", Nat(), All("x", Config(), IffF(
                Member(X("x"), Support("switchSupport", X("k"))), Some("D", Finset(Config()),
                    AndF(Member(X("D"), Reach(X("k"))), Member(X("x"), X("D")))))))))),
                "The support is the union of the sectors reached after k steps."),
            Definition("alternatingSupport", Context(FG(StartC(AndF(
                Equal(Support("alternatingSupport", D(0)), Call("Finset.coe", X("C"))),
                All("k", Nat(), All("x", Config(), IffF(Member(X("x"), Support("alternatingSupport", Add(X("k"), D(1)))),
                    Some("D", Finset(Config()), AndF(Member(X("D"), Call("sectorsOf", X("hL"), NextTwist())),
                        AndF(Member(X("x"), X("D")), Some("y", Config(), AndF(
                            Member(X("y"), Support("alternatingSupport", X("k"))), Member(X("y"), X("D")))))))))))))),
                "The recursive configuration support begins with C and at each step includes every configuration in a next-model sector containing a configuration of the preceding support."),
            Definition("twistGroup", All("N", Nat(), FG(Equal(Call("twistGroup", X("f"), X("g")),
                Call("Subgroup.closure", new Formula.SetLiteral([X("f"), X("g")]))))),
                "H is the subgroup of species permutations generated by f and g."),
            Definition("derivedTwistGroup", All("N", Nat(), FG(Equal(Call("derivedTwistGroup", X("f"), X("g")),
                Call("Subgroup.map", Call("Subgroup.subtype", TwistGroup()), Call("commutator", TwistGroup()))))),
                "The derived group is the image in the ambient permutation group of the commutator subgroup of H. This is precisely the subgroup commutator of H with itself."),
            Definition("pairTwistGroup", All("N", Nat(), FG(Equal(Call("pairTwistGroup", X("f"), X("g")),
                Call("Subgroup.closure", new Formula.SetLiteral([Pair(X("f"), Inv(X("f"))), Pair(X("g"), Inv(X("g")))]))))),
                "K is generated by the two pairs consisting of a twist and its inverse."),
            Definition("pointStabilizer", All("N", Nat(), All("H", Call("Subgroup", Perm()), All("a", Fin(X("N")),
                Equal(Call("pointStabilizer", X("H"), X("a")), Inter(X("H"), Call("MulAction.stabilizer", Perm(), X("a"))))))),
                "Intersect H with the ambient stabilizer of the species a."),
            Definition("pointPairStabilizer", All("N", Nat(), All("H", Call("Subgroup", Perm()), All("a", Fin(X("N")),
                Equal(Call("pointPairStabilizer", X("H"), X("a")), Call("Subgroup.prod",
                    Call("pointStabilizer", X("H"), X("a")), Call("pointStabilizer", X("H"), X("a"))))))),
                "Take the direct product of the two point stabilizers."),
            Definition("lTwoCriterion", All("N", Nat(), FG(IffF(Call("lTwoCriterion", X("f"), X("g")),
                All("a", Fin(X("N")), Equal(Call("Nat.card", Call("pairTwistGroup", X("f"), X("g"))),
                    Multiply(new Formula.Power(X("N"), D(2)), Call("Nat.card", Inter(
                        Call("pairTwistGroup", X("f"), X("g")), Call("pointPairStabilizer", TwistGroup(), X("a")))))))))),
                "For every a, the cardinality of K equals N squared times the cardinality of its intersection with the product stabilizer. The proof identifies this intersection with the stabilizer of the diagonal pair in K. Orbit-stabilizer then gives a full orbit."),
            Definition("lAtLeastThreeCriterion", All("N", Nat(), FG(IffF(Call("lAtLeastThreeCriterion", X("f"), X("g")),
                Call("MulAction.IsPretransitive", Call("derivedTwistGroup", X("f"), X("g")), Fin(X("N")))))),
                "For at least three sites the commutator subgroup must act transitively on the species."),
            Definition("fullSwitchingReachability", Context(FG(IffF(Call("fullSwitchingReachability", X("hL"), X("f"), X("g")),
                All("start", Q("Bool"), All("x", Config(), All("target", Config(), Some("k", Nat(),
                    Member(X("target"), Call("switchSupport", X("hL"), X("f"), X("g"), X("start"),
                        Call("sector", X("hL"), Ite(X("start"), X("f"), X("g")), X("x")), X("k")))))))))),
                "From every representative of a sector of either model, every target belongs to the support after some finite number k of alternating sector steps. Start true denotes the f-sector and start false the g-sector."),
            Definition("registeredReachabilityAnswer", Context(FG(IffF(Call("registeredReachabilityAnswer", X("hL"), X("f"), X("g")),
                IffF(Call("fullSwitchingReachability", X("hL"), X("f"), X("g")), AndF(
                    Call("unionConnected", X("hL"), X("f"), X("g")), Ite(LE(D(3), X("L")),
                        Call("lAtLeastThreeCriterion", X("f"), X("g")), Call("lTwoCriterion", X("f"), X("g")))))))),
                "The full support property is equivalent to union connectivity together with the appropriate criterion. Since hL asserts L greater than one, the alternative to L at least three is exactly L equal to two."),
            Describe.Lean(DescribeId.Create("switched-twisted-ssep-result"), DeclarationHandle.Create(Module + ".result"),
                H("The complete reachability classification"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("All natural N, all L greater than one, and every pair f,g are quantified. "
                        + "The first conjunct is the full registered answer. The second gives both directions between union connectivity and the group criterion. The third states Proposition 5.2 positivity exactly. "
                        + "The fourth identifies recursive configuration support with alternating sector closure for every finite initial set and every step count.")),
                    Paragraph(Text("For switching, each union move is absorbed by at most two alternating sector expansions, and these supports grow with the step count. "
                        + "Every expansion stays inside the starting union component. These two statements give the connectivity equivalence.")),
                    Paragraph(Text("Adjacent transpositions generate every site permutation. Composing the boundary exchange with the endpoint transposition yields a paired twist operation, "
                        + "and conjugating by site permutations places it at any distinct pair. The projection of K onto its first factor contains H. "
                        + "Lift arbitrary h and k in H onto the coordinate pairs i,j and i,k. Their commutator acts only at i. "
                        + "Subgroup.commutator_le gives every derived-group operation at each coordinate independently, which proves sufficiency when three sites are available.")),
                    Paragraph(Text("The coordinate homomorphisms are assembled with MonoidHom.pi and MonoidHom.mulSingle. "
                        + "A paired coordinate operation updates a Pi.mulSingle function at the other coordinate. "
                        + "The pair action is Prod.mulAction applied to the actions pulled back along the two projections by MulAction.compHom. "
                        + "Equiv.Perm.exists_extending_pair supplies the site permutation, and Fin.exists_ne_and_ne_of_two_lt supplies distinct auxiliary sites. "
                        + "Site and coordinate reachability subgroups are stabilizers of the union-component quotient map under arrowAction; Subgroup.copy retains their path predicates. "
                        + "Relation.EqvGen.eqvGen_le extends an elementary-move invariant to the whole union component.")),
                    Paragraph(Text("For necessity, connectivity first forces H to be transitive, since all entries of a configuration remain within the H-orbit of a constant initial species. "
                        + "Fix a species a and form the normal subgroup P given by the join of the commutator of H with the stabilizer of a. "
                        + "The quotient H/P is abelian. The charge of h acting on a is the quotient class of h; the stabilizer inclusion makes this well defined. "
                        + "Its product over all sites is invariant under exchanges and the paired twist. Connectivity to a configuration changing just one entry forces every charge to be the identity. "
                        + "Writing an element of P as a derived element times a stabilizer element proves derived-group transitivity.")),
                    Paragraph(Text("For two sites the flip sends each paired generator to its inverse, hence normalizes K and fixes every diagonal pair. "
                        + "The union component of a diagonal configuration is exactly its K-orbit. The two-site criterion follows from orbit-stabilizer and the existing Mathlib pretransitivity characterization. "
                        + "The stabilizer identification uses MulEquiv.subgroupCongr and Subgroup.subgroupOfEquivOfLe after identifying the subgroup predicates. "
                        + "The argument is uniform in the number of sites, the number of species and the two permutations."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("dabrowski-poulain-ragoucy-2026-switched-ssep-reachability"), ResolutionKind.Proved)))));

    private static Formula ResultFormula() => Context(FG(AndF(
        Call("registeredReachabilityAnswer", X("hL"), X("f"), X("g")), AndF(
            AndF(Imp(LE(D(3), X("L")), IffF(Call("unionConnected", X("hL"), X("f"), X("g")),
                Call("lAtLeastThreeCriterion", X("f"), X("g")))),
                Imp(Equal(X("L"), D(2)), IffF(Call("unionConnected", X("hL"), X("f"), X("g")),
                    Call("lTwoCriterion", X("f"), X("g"))))), AndF(
            ST(XY(IffF(Call("overlap", X("hL"), X("s"), X("t"), X("x"), X("y")),
                LT(Typed(D(0), Rat()), Call("branchingProbability", X("hL"), X("s"), X("t"), X("x"), X("y")))))),
            StartC(All("k", Nat(), Equal(Support("alternatingSupport", X("k")), Support("switchSupport", X("k"))))))))));

    private static bool IsRepositoryConstruction(string name) =>
        name is "unionMoveRelation" or "unionConnected" or "alternatingSupport" or "twistGroup"
            or "derivedTwistGroup" or "pairTwistGroup" or "pointStabilizer" or "pointPairStabilizer"
            or "lTwoCriterion" or "lAtLeastThreeCriterion" or "registeredReachabilityAnswer";

    private static DocumentBlock Definition(string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("switched-twisted-ssep-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            IsRepositoryConstruction(name)
                ? AssessedProvenance.FromRepo(Source)
                : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula LN(Formula body) => All("L", Nat(), All("N", Nat(), body));
    private static Formula Context(Formula body) => LN(All("hL", LT(D(1), X("L")), body));
    private static Formula FG(Formula body) => All("f", Perm(), All("g", Perm(), body));
    private static Formula ST(Formula body) => All("s", Perm(), All("t", Perm(), body));
    private static Formula XY(Formula body) => All("x", Config(), All("y", Config(), body));
    private static Formula StartC(Formula body) => All("start", Q("Bool"), All("C", Finset(Config()), body));
    private static Formula Config() => Call("Configuration", X("L"), X("N"));
    private static Formula Perm() => Call("Equiv.Perm", Fin(X("N")));
    private static Formula TwistGroup() => Call("twistGroup", X("f"), X("g"));
    private static Formula First() => Call("firstSite", X("hL"));
    private static Formula Last() => Call("lastSite", X("hL"));
    private static Formula Sector(string s, string x) => Call("sector", X("hL"), X(s), X(x));
    private static Formula UnionMove() => Call("unionMoveRelation", X("hL"), X("f"), X("g"), X("x"), X("y"));
    private static Formula Reach(Formula k) => Call("alternatingSectorReach", X("hL"), X("f"), X("g"), X("start"), X("C"), k);
    private static Formula Support(string name, Formula k) => Call(name, X("hL"), X("f"), X("g"), X("start"), X("C"), k);
    private static Formula NextTwist() => Ite(Equal(X("start"), Call("BEq.beq", Call("Nat.mod", X("k"), D(2)), D(0))), X("g"), X("f"));
    private static Formula Ite(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Inv(Formula value) => new Formula.Power(Parenthesized(value), Seq(Minus, D(1)));
    private static Formula Val(Formula value) => Call("Fin.val", value);
    private static Formula Card(Formula value) => Call("Finset.card", value);
    private static Formula Inter(Formula a, Formula b) => Call("inf", a, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts) { if (items.Count > 0) items.Add(Dot); items.Add(F.Id(part)); }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => Q(name);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name.Split('.')), arguments);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string n, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Lam(string n, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(n), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula OrF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
