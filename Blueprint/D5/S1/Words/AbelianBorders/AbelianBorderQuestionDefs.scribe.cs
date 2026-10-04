using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AbelianBorders;

internal sealed class AbelianBorderQuestionDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/charlier2015abelianbordered");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak abelian borders, bounded periodicity, and the geometric conditions of Question 2.",
        H("Weak Abelian Borders and Question 2"),
        Blocks(
            Node("letter-count", "Letter counts", "letterCount",
                LetterCountFormula(),
                "For words over Fin(k), letterCount(u,a) is the number of occurrences of a in u.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("weak-abelian-equivalence", "Equal letter frequencies", "WeakAbelianEquiv",
                WeakAbelianEquivFormula(),
                "Two nonempty words are weakly abelian equivalent when every letter has the same "
                    + "frequency in both words. Cross multiplication avoids division by their positive lengths.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("weak-abelian-border", "Weak abelian borders", "WeakAbelianBordered",
                WeakAbelianBorderedFormula(),
                "A border consists of a nonempty proper prefix and a nonempty suffix with equal letter "
                    + "frequencies. The suffix may be the entire word; overlaps between the prefix and suffix "
                    + "are permitted.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("word-factor", "Contiguous factors", "factor",
                FactorFormula(),
                "The factor starting at i with length n is the list of letters w(i), w(i+1), through "
                    + "w(i+n-1). The length-zero factor is empty.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("bounded-weak-abelian-periodicity", "Bounded weak abelian periodicity", "BoundedWeakAbelianPeriodic",
                BoundedWeakAbelianPeriodicFormula(),
                "After the finite prefix of length t(0), the strictly increasing cuts t partition the "
                    + "word into nonempty blocks of length at most C. Every block has the letter frequencies of "
                    + "the first block.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("prefix-parikh-vector", "Prefix Parikh vectors", "parikhPoint",
                ParikhPointFormula(),
                "The point parikhPoint(w,n) in Euclidean k-space records the counts of each letter in the "
                    + "prefix of length n, viewed as real coordinates.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("polygonal-graph", "The continuous polygonal graph", "graph",
                GraphFormula(),
                "The graph is the union, for all natural n, of the closed segments joining consecutive "
                    + "prefix Parikh vectors. It contains the full polygonal path, including points between "
                    + "cuts.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("affine-line", "An affine line", "line",
                LineFormula(),
                "The line through x0 in direction a consists of all x0+t a for real t.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("rational-axis-direction", "Rational directions", "RationalDirection",
                RationalDirectionFormula(),
                "A rational direction is a nonzero vector all of whose coordinates are rational numbers.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tangential-line", "Tangential lines", "IsTangentialLine",
                IsTangentialLineFormula(),
                "A nonzero normal b orthogonal to a defines a supporting hyperplane at height d. The "
                    + "graph meets that hyperplane, and every point of contact lies on the single axis-parallel "
                    + "line through y, which itself lies in the hyperplane.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("geometric-hypotheses", "Cylinder containment and bounded tangential gaps", "GeometricHypotheses",
                GeometricHypothesesFormula(),
                "The entire graph stays at distance at most M from a line with rational direction. For "
                    + "each tangential line there is a natural D such that every index window from n through "
                    + "n+D contains a cut point on that line; D may depend on the line.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("question-two-claim", "The positive answer to Question 2", "claim",
                ClaimFormula(),
                "Question 2 asks whether bounded weak abelian periodicity, cylinder containment with "
                    + "rational axis, and bounded gaps on each tangential line imply that only finitely many "
                    + "nonempty factors are weakly abelian unbordered. The border convention allows a "
                    + "whole-word suffix, so its finiteness conclusion is also implied by the positive answer "
                    + "under a proper-suffix convention.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula LetterCountFormula() =>
        Disp(Equal(Call("letterCount", F.Id("u"), F.Id("a")), Call("count", F.Id("u"), F.Id("a"))));

    private static Formula WeakAbelianEquivFormula() =>
        Disp(Equivalent(Call("WeakAbelianEquiv", F.Id("u"), F.Id("v")), And(NotEqual(F.Id("u"), Seq(OpenBracket,
                            CloseBracket)), And(NotEqual(F.Id("v"), Seq(OpenBracket, CloseBracket)),
                        ForAll("a", Call("Fin", F.Id("k")), Equal(Multiply(Call("length", F.Id("v")),
                                    Call("letterCount", F.Id("u"), F.Id("a"))), Multiply(Call("length",
                                        F.Id("u")), Call("letterCount", F.Id("v"), F.Id("a")))))))));

    private static Formula WeakAbelianBorderedFormula() =>
        Disp(Equivalent(Call("WeakAbelianBordered", F.Id("u")), ThereExists("r", F.Id("Nat"), ThereExists("s",
                        F.Id("Nat"), And(LessOrEqual(D(1), F.Id("r")), And(Less(F.Id("r"), Call("length",
                                        F.Id("u"))), And(LessOrEqual(D(1), F.Id("s")), And(LessOrEqual(F.Id("s"),
                                            Call("length", F.Id("u"))), Call("WeakAbelianEquiv",
                                            Call("take", F.Id("r"), F.Id("u")), Call("drop", Subtract(Call("length",
                                                F.Id("u")), F.Id("s")), F.Id("u")))))))))));

    private static Formula FactorFormula() =>
        Disp(Equal(Call("factor", F.Id("w"), F.Id("i"), F.Id("n")), Call("map", Seq(F.Id("j"), Sp,
                        Mapsto, Sp, Call("w", Add(F.Id("i"), F.Id("j")))), Call("range", F.Id("n")))));

    private static Formula BoundedWeakAbelianPeriodicFormula() =>
        Disp(Equivalent(Call("BoundedWeakAbelianPeriodic", F.Id("w")), ThereExists("t", Seq(F.Id("Nat"),
                        To, Sp, F.Id("Nat")), ThereExists("C", F.Id("Nat"), And(Call("StrictMono",
                                F.Id("t")), And(ForAll("i", F.Id("Nat"), LessOrEqual(Subtract(Call("t",
                                                Add(F.Id("i"), D(1))), Call("t", F.Id("i"))), F.Id("C"))),
                                ForAll("i", F.Id("Nat"), Call("WeakAbelianEquiv", Call("factor",
                                            F.Id("w"), Call("t", F.Id("i")), Subtract(Call("t", Add(F.Id("i"),
                                                D(1))), Call("t", F.Id("i")))), Call("factor", F.Id("w"),
                                            Call("t", D(0)), Subtract(Call("t", D(1)), Call("t",
                                                D(0))))))))))));

    private static Formula ParikhPointFormula() =>
        Disp(ForAll("a", Call("Fin", F.Id("k")), Equal(Call("coordinate", Call("parikhPoint", F.Id("w"),
                            F.Id("n")), F.Id("a")), Call("castReal", Call("letterCount", Call("factor",
                                F.Id("w"), D(0), F.Id("n")), F.Id("a"))))));

    private static Formula GraphFormula() =>
        Disp(Equal(Call("graph", F.Id("w")), Call("iUnion", Seq(F.Id("n"), Sp, Mapsto, Sp, Call("segment",
                            Call("parikhPoint", F.Id("w"), F.Id("n")), Call("parikhPoint", F.Id("w"),
                                Add(F.Id("n"), D(1))))))));

    private static Formula LineFormula() =>
        Disp(Equal(Call("line", F.Id("x0"), F.Id("a")), Seq(OpenBrace, Sp, F.Id("x"), Colon, Sp,
                    Call("EuclideanSpace", F.Id("Real"), Call("Fin", F.Id("k"))), Sp, Mid, Sp, ThereExists("t",
                        F.Id("Real"), Equal(F.Id("x"), Add(F.Id("x0"), Scale(F.Id("t"), F.Id("a"))))),
                    CloseBrace, Sp)));

    private static Formula RationalDirectionFormula() =>
        Disp(Equivalent(Call("RationalDirection", F.Id("a")), And(NotEqual(F.Id("a"), D(0)), ForAll("i",
                        Call("Fin", F.Id("k")), ThereExists("q", F.Id("Rat"), Equal(Call("coordinate",
                                    F.Id("a"), F.Id("i")), Call("castReal", F.Id("q"))))))));

    private static Formula IsTangentialLineFormula() =>
        Disp(Equivalent(Call("IsTangentialLine", F.Id("w"), F.Id("a"), F.Id("y")), ThereExists("b",
                    Call("EuclideanSpace", F.Id("Real"), Call("Fin", F.Id("k"))), ThereExists("d",
                        F.Id("Real"), And(NotEqual(F.Id("b"), D(0)), And(Equal(Call("inner", F.Id("b"),
                                        F.Id("a")), D(0)), And(ForAll("x", Call("EuclideanSpace",
                                            F.Id("Real"), Call("Fin", F.Id("k"))), Implies(Member(F.Id("x"),
                                                Call("graph", F.Id("w"))), LessOrEqual(F.Id("d"),
                                                Call("inner", F.Id("b"), F.Id("x"))))), And(ThereExists("x",
                                            Call("EuclideanSpace", F.Id("Real"), Call("Fin", F.Id("k"))),
                                            And(Member(F.Id("x"), Call("graph", F.Id("w"))), Equal(Call("inner",
                                                F.Id("b"), F.Id("x")), F.Id("d")))), And(Call("Subset",
                                                Call("line", F.Id("y"), F.Id("a")), Seq(OpenBrace,
                                                Sp, F.Id("x"), Colon, Sp, Call("EuclideanSpace",
                                                F.Id("Real"), Call("Fin", F.Id("k"))), Sp, Mid, Sp,
                                                Equal(Call("inner", F.Id("b"), F.Id("x")), F.Id("d")),
                                                CloseBrace, Sp)), ForAll("x", Call("EuclideanSpace",
                                                F.Id("Real"), Call("Fin", F.Id("k"))), Implies(Member(F.Id("x"),
                                                Call("graph", F.Id("w"))), Implies(Equal(Call("inner",
                                                F.Id("b"), F.Id("x")), F.Id("d")), Member(F.Id("x"),
                                                Call("line", F.Id("y"), F.Id("a")))))))))))))));

    private static Formula GeometricHypothesesFormula() =>
        Disp(Equivalent(Call("GeometricHypotheses", F.Id("w")), ThereExists("x0", Call("EuclideanSpace",
                        F.Id("Real"), Call("Fin", F.Id("k"))), ThereExists("a", Call("EuclideanSpace",
                            F.Id("Real"), Call("Fin", F.Id("k"))), ThereExists("M", F.Id("Real"),
                            And(Call("RationalDirection", F.Id("a")), And(ForAll("x", Call("EuclideanSpace",
                                            F.Id("Real"), Call("Fin", F.Id("k"))), Implies(Member(F.Id("x"),
                                                Call("graph", F.Id("w"))), LessOrEqual(Call("infDist",
                                                F.Id("x"), Call("line", F.Id("x0"), F.Id("a"))),
                                                F.Id("M")))), ForAll("y", Call("EuclideanSpace",
                                            F.Id("Real"), Call("Fin", F.Id("k"))), Implies(Call("IsTangentialLine",
                                                F.Id("w"), F.Id("a"), F.Id("y")), ThereExists("D",
                                                F.Id("Nat"), ForAll("n", F.Id("Nat"), ThereExists("m",
                                                F.Id("Nat"), And(LessOrEqual(F.Id("n"), F.Id("m")),
                                                And(LessOrEqual(F.Id("m"), Add(F.Id("n"), F.Id("D"))),
                                                Member(Call("parikhPoint", F.Id("w"), F.Id("m")),
                                                Call("line", F.Id("y"), F.Id("a")))))))))))))))));

    private static Formula ClaimFormula() =>
        Disp(Equivalent(F.Id("claim"), ForAll("k", F.Id("Nat"), ForAll("w", Seq(F.Id("Nat"), To,
                            Sp, Call("Fin", F.Id("k"))), Implies(Call("BoundedWeakAbelianPeriodic",
                                F.Id("w")), Implies(Call("GeometricHypotheses", F.Id("w")), Call("Finite",
                                    Seq(OpenBrace, Sp, F.Id("u"), Colon, Sp, Call("List", Call("Fin",
                                                F.Id("k"))), Sp, Mid, Sp, And(ThereExists("i", F.Id("Nat"),
                                                ThereExists("n", F.Id("Nat"), Equal(F.Id("u"), Call("factor",
                                                F.Id("w"), F.Id("i"), F.Id("n"))))), And(NotEqual(F.Id("u"),
                                                Seq(OpenBracket, CloseBracket)), Negated(Call("WeakAbelianBordered",
                                                F.Id("u"))))), CloseBrace, Sp))))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ThereExists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Negated(Formula value) => new Formula.Not(Seq(Open, value, Close));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Scale(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
