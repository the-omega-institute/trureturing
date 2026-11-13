using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricOcticRanksDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Algebra/AuricOcticRanks.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Some(string names, Formula type, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse())
            body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
        return body;
    }
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => Rel(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(Seq(Open, x, Close), op, Seq(Open, y, Close));
    private static Formula And(params Formula[] xs) =>
        xs.Reverse().Aggregate((x, y) => Logic(y, FormulaLogicOperator.And, x));
    private static Formula Imp(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Instance(string name, params Formula[] xs) => Seq(OpenBracket, Call(name, xs), CloseBracket, Sp);
    private static Formula K => V("K");
    private static Formula O => V("Omega");
    private static Formula G => V("G");
    private static Formula U => V("U");
    private static Formula S => V("S");
    private static Formula C(Formula s) => Call("compl", s);
    private static Formula R(Formula s) => Call("rowRank", U, s);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Sets => Call("Finset", O);
    private static Formula Coordinates => Call("Map", O, K);
    private static Formula Operators => Call("LinearMap", K, Coordinates, Coordinates);
    private static Formula Context(Formula body) => All("K Omega", V("Type"), Seq(
        Instance("Field", K), Instance("Fintype", O), Instance("DecidableEq", O),
        All("U", Call("Submodule", K, Coordinates), body)));
    private static Formula Action(Formula body) => All("G", V("Type"), Seq(
        Instance("Group", G), Instance("Fintype", G), Instance("MulAction", G, O), body));
    private static Formula Transitive => All("x y", O, Some("g", G,
        Equal(Call("act", V("g"), V("x")), V("y"))));
    private static Formula Invariant => All("g", G, All("T", Sets,
        Equal(R(Call("orbitSet", V("T"), V("g"))), R(V("T")))));
    private static Formula Strict => All("T", Sets, Imp(
        And(Less(D(0), Card(V("T"))), Less(Card(V("T")), D(8))),
        Leq(Add(Card(V("T")), D(1)), Mul(D(2), R(V("T"))))));
    private static Formula Cut(Formula n) => All("S", Sets, Imp(
        And(Leq(D(2), Card(S)), Leq(Card(S), D(6))),
        Logic(Leq(D(2), Call("crossRank", n, S)), FormulaLogicOperator.Or,
            Leq(D(2), Call("crossRank", n, C(S))))));
    private static DocumentBlock.Describe Dsc(string name, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    public DocumentDefinition Create()
    {
        var projected = Dsc("projected_disjoint", "Complementary coordinate images are disjoint",
            Context(All("S", Sets, Call("Disjoint", Call("projected", U, S), Call("projected", U, C(S))))),
            "projected(U,S) is the image of U under the coordinate projection retaining S. The two images "
            + "have disjoint coordinate supports. This gives one of the two dimension identities used in window connectivity.");
        var containment = Dsc("window_le_projected_sup", "The window lies in the sum of its projected images",
            Context(All("S", Sets, Rel(U, FormulaRelationOperator.SubsetOf,
                Call("sup", Call("projected", U, S), Call("projected", U, C(S)))))),
            "Every vector is the sum of its two complementary coordinate projections. Together with "
            + "complementary disjointness, this bounds the window dimension by the sum of the projection dimensions.");
        var equality = Dsc("projection_stable_of_rank_equality", "Complementary rank equality forces projection stability",
            Context(All("S", Sets, Imp(Equal(Add(R(S), R(C(S))), Call("finrank", K, U)),
                All("x", Coordinates, Imp(Mem(V("x"), U), Mem(Call("coordinateProject", S, V("x")), U)))))),
            "rowRank(U,S) is the dimension of projected(U,S). Equality in the complementary dimension "
            + "bound makes U equal the direct sum of those images. Its S projection therefore preserves U. "
            + "The actual scalar-idealizer argument uses this conclusion to exclude equality.");
        var orbit = Dsc("mem_orbitSet", "Membership in an actual translate",
            All("Omega G", V("Type"), Seq(Instance("Fintype", O), Instance("DecidableEq", O),
                Instance("Group", G), Instance("Fintype", G), Instance("MulAction", G, O),
                All("S", Sets, All("g", G, All("i", O, Logic(
                    Mem(V("i"), Call("orbitSet", S, V("g"))), FormulaLogicOperator.Iff,
                    Mem(Call("act", Call("inverse", V("g")), V("i")), S))))))),
            "orbitSet(S,g) is the image of S under the action of g. This identity "
            + "connects the Galois semilinear coordinate map to the translated projection.");
        var connected = All("T", Sets, Imp(And(Call("Nonempty", V("T")), Call("Nonempty", C(V("T")))),
            Less(D(4), Add(R(V("T")), R(C(V("T")))))));
        var strict = Dsc("invariant_half_rank_strict", "Connected transitive half-ranks are strictly balanced",
            Context(Action(Imp(And(Equal(Call("card", O), D(8)), Equal(Call("finrank", K, U), D(4)),
                Transitive, Invariant, connected), All("S", Sets,
                Imp(And(Call("Nonempty", S), Call("Nonempty", C(S))),
                    Leq(Add(Card(S), D(1)), Mul(D(2), R(S)))))))),
            "The fractional_submodular_cover theorem is applied to translates of S with their "
            + "constant covering multiplicity to obtain the weak half-rank bound. For the nonnegative "
            + "invariant submodular defect 2 rowRank minus cardinality, a minimal nonempty zero set has "
            + "translates that cannot cross any zero set. Transitivity covers the complement by such "
            + "translates, so equality on S forces equality on its complement. Connectedness excludes "
            + "both equalities. This equality-rigidity argument supplies the strict-rank bound for "
            + "the actual split window.");
        var matrix = Dsc("crossRank_matrix", "Operator crossing rank equals its literal matrix block rank",
            All("K Omega", V("Type"), Seq(Instance("Field", K), Instance("Fintype", O), Instance("DecidableEq", O),
                All("n", Operators, All("S", Sets, Equal(
                    Call("rank", Call("block", Call("toMatrix", V("n")), S, C(S))),
                    Call("crossRank", V("n"), S)))))),
            "crossRank(n,S) is the dimension of the image of extension by zero from S complement, "
            + "followed by n and projection to S. The literal subtype-indexed matrix block represents "
            + "that map; extension by zero in the target is injective. The actual cut-free endpoint "
            + "uses this identity to state its conclusion using the actual matrix entries.");
        var cut = Dsc("cut_free_of_actual_ranks", "Transitive strict half-ranks exclude a cut on eight labels",
            Context(Action(All("n", Operators, Imp(And(Equal(Call("ker", V("n")), U),
                Equal(Call("range", V("n")), U), Equal(Call("card", O), D(8)),
                Equal(Call("finrank", K, U), D(4)), Transitive, Invariant, Strict), Cut(V("n")))))),
            "Rank-nullity bounds 2 rowRank(U,S) by card(S) plus crossRank(n,S). If both crossing ranks "
            + "were at most one for a cut of size two through six, the strict lower bounds force a "
            + "three-element side of rank two with complement of rank three. Submodularity and strict "
            + "rank imply that two translates of this triple are equal or disjoint, using the complement "
            + "when the intersection has one element. Transitivity then partitions eight labels into "
            + "triples, which is impossible. The actual-window theorem supplies every premise from its "
            + "original window; it does not assume this rank model as additional data.");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The rank arguments consumed by the actual octic window theorem.", H("Invariant octic rank rigidity"),
            Blocks(Paragraph(Text(
                "All statements concern finite coordinate labels over an arbitrary field. Group actions "
                + "are finite and literal. toMatrix is the standard coordinate matrix; block uses the "
                + "indicated row and column subtypes. These symbolic dimension and orbit arguments are "
                + "not a finite certified instance or enumeration. The source is the rank and cut argument "
                + "of general section 43.2, together with the strict-rank mechanism of section 26. "
                + "No mathematical novelty is claimed.")), projected, containment, equality, orbit, strict, matrix, cut)));
    }
}
