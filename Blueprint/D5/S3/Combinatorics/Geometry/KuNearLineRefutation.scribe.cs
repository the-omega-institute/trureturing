using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class KuNearLineRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/KuNearLineRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/ku2026monochromatic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary integer-board line avoidance forces a strict upper bound on maximal saturated density.",
        H("Near-Line Avoidance on the Three-Dimensional Board"),
        Blocks(
            Node("statement0", "Three coordinate values", "C", Formula0(),
                "The coordinate labels are zero, one and two.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement1", "Twenty-seven points", "P", Formula1(),
                "A point has three coordinates, each with three possible values.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement2", "Ordinary integer coordinates", "coord", Formula2(),
                "Adding one identifies coordinate labels with the integers from one through three. Throughout, val is Fin.val, apply is function application, and (n : Z), displayed with the integer symbol, denotes the canonical natural-to-integer cast.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement3", "Full signed ordinary line", "Valid", Formula3(),
                "A direction is nonzero, each direction coordinate is minus one, zero or one, and all three parameter points stay inside the integer board.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement4", "Incidence", "On", Formula4(),
                "Incidence uses ordinary integer addition and multiplication at a parameter in Fin 3.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement5", "A common full line", "Common", Formula5(),
                "Two points are related when a single admissible full line contains both.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement6", "Pairwise line avoidance", "Config", Formula6(),
                "A configuration has at most one point on every full three-line.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement7", "Axis-parallel line", "axis_common", Formula7(),
                "Points that agree away from one coordinate lie on a full axis-parallel line.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement8", "Face-diagonal line", "diag_common", Formula8(),
                "Equal third coordinates and membership in the same main or opposite face diagonal give an ordinary full line.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement9", "Latin square predicate", "Latin", Formula9(),
                "The Latin predicate is the existing row-and-column bijectivity predicate.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement10", "Order-three diagonal collision", "latin_diagonal", Formula10(),
                "Every Latin square of order three repeats a symbol on at least one of its two diagonals. Subtraction here is in Fin 3; the opposite diagonal is also characterized by the sum of the natural coordinate values being two.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement11", "Eight-point bound", "config_bound", Formula11(),
                "Projection to the first two coordinates is injective. Equality at nine points would give a Latin square of order three; its diagonal collision contradicts line avoidance.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement12", "Near-three-line avoidance", "SourceConfig", Formula12(),
                "No two-element subset of any admissible full three-line can be contained in the configuration.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement13", "Pairwise and near-line descriptions", "source_config_iff", Formula13(),
                "The source subset condition is equivalent to pairwise avoidance.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement14", "General ordinary board", "Board", Formula14(),
                "The board has d coordinates, each labeled by Fin k and interpreted as integers by adding one. Its cardinality is k raised to d.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement15", "General full signed line", "GValid", Formula15(),
                "Every signed nonzero direction and every parameter from zero through k minus one are included.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement16", "General incidence", "GOn", Formula16(),
                "General incidence uses the same ordinary integer coordinate map.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement17", "Intersection cardinality condition", "GConfig", Formula17(),
                "Every line contains at most k minus two selected points.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement18", "Near-line subset condition", "GSourceConfig", Formula18(),
                "No subset of cardinality k minus one lying on a full line is selected in its entirety.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement19", "General source equivalence", "gsource_config_iff", Formula19(),
                "For k at least two, the forbidden-subset and intersection-cardinality descriptions agree.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement20", "Three-dimensional specialization", "gconfig_33_iff", Formula20(),
                "At k equal to three and dimension three, the general configuration is exactly the pairwise geometric configuration.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement21", "Inclusion maximality", "GSaturated", Formula21(),
                "A saturated configuration cannot be enlarged while retaining near-line avoidance.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement22", "A cardinality maximizer exists", "gexists_opt", Formula22(),
                "The finite family of configurations is nonempty because it contains the empty set. A cardinality maximum therefore exists.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement23", "Chosen cardinality maximizer", "gopt", Formula23(),
                "The proof h has exactly the existential type displayed. In the source it is gexists_opt k d; proof irrelevance identifies any proof h of that proposition with this source proof, so Classical.choose h is exactly the defining choice, not a choice applied to a proposition.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("statement24", "Maximizer specification", "gopt_spec", Formula24(),
                "The selected set is a configuration and its cardinality dominates every configuration.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement25", "A maximum is saturated", "gopt_saturated", Formula25(),
                "Any configuration containing the cardinality maximizer has equal cardinality and hence is the same set.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement26", "Maximum density", "density", Formula26(),
                "The proof h has exactly the displayed saturated-maximum existential type; the source uses density_maximum_attained k d. Proof irrelevance makes Classical.choose h the same defining choice. Parenthesized type annotations with the real symbol denote canonical natural-to-real casts. Divide the selected cardinality by k raised to d; for k at least two the denominator is positive, giving exactly the maximum saturated density.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement27", "Attained saturated maximum", "density_maximum_attained", Formula27(),
                "A saturated configuration has cardinality at least that of every saturated configuration. Choosing from this nonempty finite maximizing family defines the density.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement28", "Strict density bound", "exact_real_event", Formula28(),
                "The saturated maximizer has at most eight points out of twenty-seven, strictly below one third. No exact maximum or prescribed size-eight attainer is asserted.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("statement29", "Conjecture 5.6", "claim", Formula29(),
                "The conjecture asserts the same density formula for every k at least two and every natural dimension. The real type annotation denotes the canonical natural-to-real cast. The parameter pair three, three belongs to either convention for natural dimensions.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("statement30", "Refutation", "result", Formula30(),
                "At k equal to three and dimension three, the asserted equality contradicts the strict bound.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ku-2026-monochromatic-k-in-a-row-conjecture-5-6"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsF(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula LeF(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtF(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Subset(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.SubsetOf, y);
    private static Formula IffF(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula OrF(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Or, y);
    private static Formula AndF(params Formula[] xs) { var r = xs[^1]; for (var i = xs.Length - 2; i >= 0; i--) r = new Formula.Logic(xs[i], FormulaLogicOperator.And, r); return r; }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula NotF(Formula x) => Seq(Neg, Sp, Parenthesized(x));
    private static Formula IntegerCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z")))));
    private static Formula RealCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))));
    private static Formula ChooseF(Formula proof) => new Formula.Apply(Seq(F.Id("Classical"), Dot, F.Id("choose")), [proof]);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula FracF(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, F.Id(name), Colon, type, Sp, Bar, Sp, body, CloseBrace);
    private static Formula Formula0() => Disp(Eq(Call("C"), Call("Fin", D(3))));
    private static Formula Formula1() => Disp(Eq(Call("P"), Arrow(Call("Fin", D(3)), Call("C"))));
    private static Formula Formula2() => Disp(All("a", Call("P"), All("i", Call("Fin", D(3)), Eq(Call("coord", F.Id("a"), F.Id("i")), Add(IntegerCast(Call("val", Call("apply", F.Id("a"), F.Id("i")))), D(1))))));
    private static Formula Formula3() => Disp(All("s", Arrow(Call("Fin", D(3)), Call("Int")), All("v", Arrow(Call("Fin", D(3)), Call("Int")), IffF(Call("Valid", F.Id("s"), F.Id("v")), AndF(ExistsF("i", Call("Fin", D(3)), Ne(Call("apply", F.Id("v"), F.Id("i")), D(0))), All("i", Call("Fin", D(3)), OrF(Eq(Call("apply", F.Id("v"), F.Id("i")), Seq(Minus, D(1))), OrF(Eq(Call("apply", F.Id("v"), F.Id("i")), D(0)), Eq(Call("apply", F.Id("v"), F.Id("i")), D(1))))), All("t", Call("Fin", D(3)), All("i", Call("Fin", D(3)), AndF(LeF(D(1), Add(Call("apply", F.Id("s"), F.Id("i")), Mul(IntegerCast(Call("val", F.Id("t"))), Call("apply", F.Id("v"), F.Id("i"))))), LeF(Add(Call("apply", F.Id("s"), F.Id("i")), Mul(IntegerCast(Call("val", F.Id("t"))), Call("apply", F.Id("v"), F.Id("i")))), IntegerCast(D(3)))))))))));
    private static Formula Formula4() => Disp(All("a", Call("P"), All("s", Arrow(Call("Fin", D(3)), Call("Int")), All("v", Arrow(Call("Fin", D(3)), Call("Int")), IffF(Call("On", F.Id("a"), F.Id("s"), F.Id("v")), ExistsF("t", Call("Fin", D(3)), All("i", Call("Fin", D(3)), Eq(Call("coord", F.Id("a"), F.Id("i")), Add(Call("apply", F.Id("s"), F.Id("i")), Mul(IntegerCast(Call("val", F.Id("t"))), Call("apply", F.Id("v"), F.Id("i"))))))))))));
    private static Formula Formula5() => Disp(All("a", Call("P"), All("b", Call("P"), IffF(Call("Common", F.Id("a"), F.Id("b")), ExistsF("s", Arrow(Call("Fin", D(3)), Call("Int")), ExistsF("v", Arrow(Call("Fin", D(3)), Call("Int")), AndF(Call("Valid", F.Id("s"), F.Id("v")), Call("On", F.Id("a"), F.Id("s"), F.Id("v")), Call("On", F.Id("b"), F.Id("s"), F.Id("v")))))))));
    private static Formula Formula6() => Disp(All("S", Call("Finset", Call("P")), IffF(Call("Config", F.Id("S")), All("a", Call("P"), All("b", Call("P"), Imp(Mem(F.Id("a"), F.Id("S")), Imp(Mem(F.Id("b"), F.Id("S")), Imp(Call("Common", F.Id("a"), F.Id("b")), Eq(F.Id("a"), F.Id("b"))))))))));
    private static Formula Formula7() => Disp(All("a", Call("P"), All("b", Call("P"), All("j", Call("Fin", D(3)), Imp(All("i", Call("Fin", D(3)), Imp(Ne(F.Id("i"), F.Id("j")), Eq(Call("apply", F.Id("a"), F.Id("i")), Call("apply", F.Id("b"), F.Id("i"))))), Call("Common", F.Id("a"), F.Id("b")))))));
    private static Formula Formula8() => Disp(All("a", Call("P"), All("b", Call("P"), Imp(Eq(Call("apply", F.Id("a"), D(2)), Call("apply", F.Id("b"), D(2))), Imp(OrF(AndF(Eq(Call("apply", F.Id("a"), D(0)), Call("apply", F.Id("a"), D(1))), Eq(Call("apply", F.Id("b"), D(0)), Call("apply", F.Id("b"), D(1)))), AndF(Eq(Add(Call("val", Call("apply", F.Id("a"), D(0))), Call("val", Call("apply", F.Id("a"), D(1)))), D(2)), Eq(Add(Call("val", Call("apply", F.Id("b"), D(0))), Call("val", Call("apply", F.Id("b"), D(1)))), D(2)))), Call("Common", F.Id("a"), F.Id("b")))))));
    private static Formula Formula9() => Disp(All("n", Call("Nat"), All("L", Arrow(Call("Fin", F.Id("n")), Arrow(Call("Fin", F.Id("n")), Call("Fin", F.Id("n")))), IffF(Call("Latin", F.Id("n"), F.Id("L")), Call("IsLatin", F.Id("n"), F.Id("L"))))));
    private static Formula Formula10() => Disp(All("L", Arrow(Call("C"), Arrow(Call("C"), Call("C"))), Imp(Call("Latin", D(3), F.Id("L")), ExistsF("i", Call("C"), ExistsF("j", Call("C"), AndF(Ne(F.Id("i"), F.Id("j")), OrF(Eq(Call("apply", F.Id("L"), F.Id("i"), F.Id("i")), Call("apply", F.Id("L"), F.Id("j"), F.Id("j"))), Eq(Call("apply", F.Id("L"), F.Id("i"), Sub(D(2), F.Id("i"))), Call("apply", F.Id("L"), F.Id("j"), Sub(D(2), F.Id("j")))))))))));
    private static Formula Formula11() => Disp(All("S", Call("Finset", Call("P")), Imp(Call("Config", F.Id("S")), LeF(Call("card", F.Id("S")), D(8)))));
    private static Formula Formula12() => Disp(All("S", Call("Finset", Call("P")), IffF(Call("SourceConfig", F.Id("S")), All("s", Arrow(Call("Fin", D(3)), Call("Int")), All("v", Arrow(Call("Fin", D(3)), Call("Int")), Imp(Call("Valid", F.Id("s"), F.Id("v")), All("N", Call("Finset", Call("P")), Imp(Eq(Call("card", F.Id("N")), D(2)), Imp(All("a", Call("P"), Imp(Mem(F.Id("a"), F.Id("N")), Call("On", F.Id("a"), F.Id("s"), F.Id("v")))), NotF(Subset(F.Id("N"), F.Id("S"))))))))))));
    private static Formula Formula13() => Disp(All("S", Call("Finset", Call("P")), IffF(Call("SourceConfig", F.Id("S")), Call("Config", F.Id("S")))));
    private static Formula Formula14() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), Eq(Call("Board", F.Id("k"), F.Id("d")), Arrow(Call("Fin", F.Id("d")), Call("Fin", F.Id("k")))))));
    private static Formula Formula15() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("s", Arrow(Call("Fin", F.Id("d")), Call("Int")), All("v", Arrow(Call("Fin", F.Id("d")), Call("Int")), IffF(Call("GValid", F.Id("k"), F.Id("d"), F.Id("s"), F.Id("v")), AndF(ExistsF("i", Call("Fin", F.Id("d")), Ne(Call("apply", F.Id("v"), F.Id("i")), D(0))), All("i", Call("Fin", F.Id("d")), OrF(Eq(Call("apply", F.Id("v"), F.Id("i")), Seq(Minus, D(1))), OrF(Eq(Call("apply", F.Id("v"), F.Id("i")), D(0)), Eq(Call("apply", F.Id("v"), F.Id("i")), D(1))))), All("t", Call("Fin", F.Id("k")), All("i", Call("Fin", F.Id("d")), AndF(LeF(D(1), Add(Call("apply", F.Id("s"), F.Id("i")), Mul(IntegerCast(Call("val", F.Id("t"))), Call("apply", F.Id("v"), F.Id("i"))))), LeF(Add(Call("apply", F.Id("s"), F.Id("i")), Mul(IntegerCast(Call("val", F.Id("t"))), Call("apply", F.Id("v"), F.Id("i")))), IntegerCast(F.Id("k")))))))))))));
    private static Formula Formula16() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("a", Call("Board", F.Id("k"), F.Id("d")), All("s", Arrow(Call("Fin", F.Id("d")), Call("Int")), All("v", Arrow(Call("Fin", F.Id("d")), Call("Int")), IffF(Call("GOn", F.Id("a"), F.Id("s"), F.Id("v")), ExistsF("t", Call("Fin", F.Id("k")), All("i", Call("Fin", F.Id("d")), Eq(Add(IntegerCast(Call("val", Call("apply", F.Id("a"), F.Id("i")))), D(1)), Add(Call("apply", F.Id("s"), F.Id("i")), Mul(IntegerCast(Call("val", F.Id("t"))), Call("apply", F.Id("v"), F.Id("i"))))))))))))));
    private static Formula Formula17() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), IffF(Call("GConfig", F.Id("S")), All("s", Arrow(Call("Fin", F.Id("d")), Call("Int")), All("v", Arrow(Call("Fin", F.Id("d")), Call("Int")), Imp(Call("GValid", F.Id("k"), F.Id("d"), F.Id("s"), F.Id("v")), LeF(Call("card", SetOf("a", Call("Board", F.Id("k"), F.Id("d")), AndF(Mem(F.Id("a"), F.Id("S")), Call("GOn", F.Id("a"), F.Id("s"), F.Id("v"))))), Sub(F.Id("k"), D(2)))))))))));
    private static Formula Formula18() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), IffF(Call("GSourceConfig", F.Id("S")), All("s", Arrow(Call("Fin", F.Id("d")), Call("Int")), All("v", Arrow(Call("Fin", F.Id("d")), Call("Int")), Imp(Call("GValid", F.Id("k"), F.Id("d"), F.Id("s"), F.Id("v")), All("N", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Eq(Call("card", F.Id("N")), Sub(F.Id("k"), D(1))), Imp(All("a", Call("Board", F.Id("k"), F.Id("d")), Imp(Mem(F.Id("a"), F.Id("N")), Call("GOn", F.Id("a"), F.Id("s"), F.Id("v")))), NotF(Subset(F.Id("N"), F.Id("S"))))))))))))));
    private static Formula Formula19() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), Imp(LeF(D(2), F.Id("k")), All("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), IffF(Call("GSourceConfig", F.Id("S")), Call("GConfig", F.Id("S"))))))));
    private static Formula Formula20() => Disp(All("S", Call("Finset", Call("P")), IffF(Call("GConfig", F.Id("S")), Call("Config", F.Id("S")))));
    private static Formula Formula21() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), IffF(Call("GSaturated", F.Id("S")), AndF(Call("GConfig", F.Id("S")), All("T", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Call("GConfig", F.Id("T")), Imp(Subset(F.Id("S"), F.Id("T")), Eq(F.Id("T"), F.Id("S")))))))))));
    private static Formula Formula22() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), ExistsF("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), AndF(Call("GConfig", F.Id("S")), All("T", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Call("GConfig", F.Id("T")), LeF(Call("card", F.Id("T")), Call("card", F.Id("S"))))))))));
    private static Formula Formula23() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("h", ExistsF("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), AndF(Call("GConfig", F.Id("S")), All("T", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Call("GConfig", F.Id("T")), LeF(Call("card", F.Id("T")), Call("card", F.Id("S"))))))), Eq(Call("gopt", F.Id("k"), F.Id("d")), ChooseF(F.Id("h")))))));
    private static Formula Formula24() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), AndF(Call("GConfig", Call("gopt", F.Id("k"), F.Id("d"))), All("T", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Call("GConfig", F.Id("T")), LeF(Call("card", F.Id("T")), Call("card", Call("gopt", F.Id("k"), F.Id("d"))))))))));
    private static Formula Formula25() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), Call("GSaturated", Call("gopt", F.Id("k"), F.Id("d"))))));
    private static Formula Formula26() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), All("h", ExistsF("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), AndF(Call("GSaturated", F.Id("S")), All("T", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Call("GSaturated", F.Id("T")), LeF(Call("card", F.Id("T")), Call("card", F.Id("S"))))))), Eq(Call("density", F.Id("k"), F.Id("d")), FracF(RealCast(Call("card", ChooseF(F.Id("h")))), Pow(RealCast(F.Id("k")), F.Id("d"))))))));
    private static Formula Formula27() => Disp(All("k", Call("Nat"), All("d", Call("Nat"), ExistsF("S", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), AndF(Call("GSaturated", F.Id("S")), All("T", Call("Finset", Call("Board", F.Id("k"), F.Id("d"))), Imp(Call("GSaturated", F.Id("T")), LeF(Call("card", F.Id("T")), Call("card", F.Id("S"))))))))));
    private static Formula Formula28() => Disp(LtF(Call("density", D(3), D(3)), FracF(D(1), D(3))));
    private static Formula Formula29() => Disp(IffF(Call("claim"), All("k", Call("Nat"), Imp(LeF(D(2), F.Id("k")), All("d", Call("Nat"), Eq(Call("density", F.Id("k"), F.Id("d")), Sub(D(1), FracF(D(2), RealCast(F.Id("k"))))))))));
    private static Formula Formula30() => Disp(NotF(Call("claim")));
}
