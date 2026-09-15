using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class PellClassSuccessorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/PellClassSuccessor.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/wu2026a399755");
    private static readonly LibraryNoteRef Classes =
        LibraryNoteRef.Create("D5/L/robertson2004generalizedpell");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least square partner and integral-unit classes of the norm-(k^2+1) equation.",
        H("Wu's Pell-Class Successor Criterion"),
        Blocks(
            Node(
                "Discriminant", "The integer parameter", DiscriminantFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The parameter k is a natural number, and Discriminant(k) is an integer. "
                    + "IntOfNat denotes the canonical inclusion of natural numbers into the integers. "
                    + "The defining formula applies to every natural k; positivity is a hypothesis "
                    + "of the final statement.",
                DescribeRole.Definition),
            Node(
                "Sol", "Integral solutions of the generalized Pell equation", SolFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Sol(k,x,y) expresses the equation in the A399755 name, with its right-hand "
                    + "side written as Discriminant(k). Both coordinates range over all integers. "
                    + "There is no primitive-solution or squarefree-parameter restriction.",
                DescribeRole.Definition),
            Node(
                "SameClass", "Equivalence under integral norm-one units", SameClassFormula(),
                AssessedProvenance.FromLiterature(Classes),
                "On solutions of the same generalized Pell equation, SameClass is the "
                    + "integral-unit relation of the section on the structure of solutions, "
                    + "pages 12 through 14. The unit coordinates u and v are integers and their "
                    + "norm is one. In particular, u=-1 and v=0 are allowed, so simultaneous "
                    + "negation preserves the class. The relation does not identify arbitrary "
                    + "independent sign changes, and does not enlarge the units to fractional "
                    + "coordinates in a maximal order. SameClass itself records the unit action; "
                    + "the Sol conditions are supplied explicitly in MultipleClasses.",
                DescribeRole.Definition),
            Node(
                "MultipleClasses", "More than one generalized solution class", MultipleClassesFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A399755 membership means that two integral solutions lie in different classes "
                    + "under SameClass. The classical convention selects one fundamental "
                    + "representative per generalized solution class. This is distinct from the "
                    + "fundamental positive solution of the norm-one equation. The versioned "
                    + "SymPy diop_DN docstring's one-tuple-per-class convention is a semantic "
                    + "reference for the source program; no execution of that program is a "
                    + "mathematical premise. Membership concerns the integer k itself, not the "
                    + "kth listed value of A399755.",
                DescribeRole.Definition),
            Node(
                "NextSquarePartner", "The least larger square partner", NextSquarePartnerFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The companion A399491 definition selects the least natural m greater than k "
                    + "for which the displayed product is a square. IsSquare is the square "
                    + "predicate on natural numbers. The universal condition compares m with "
                    + "every larger candidate n satisfying the same square predicate. Thus the "
                    + "definition includes both admissibility and the entire minimum condition; "
                    + "existence is asserted separately in the final statement.",
                DescribeRole.Definition),
            Node(
                "result", "The least-partner existence and strict cubic equivalence", ResultFormula(),
                AssessedProvenance.FromRepo(Source, Classes),
                "The statement concerns every positive natural k. It asserts the existence of "
                    + "a least square partner m and identifies the strict inequality below the "
                    + "cubic bound with the presence of more than one integral-unit class. "
                    + "Both directions use the same least partner. The named source conjecture "
                    + "supplies the equivalence to be addressed, while the existential quantifier "
                    + "makes explicit the totality implicit in A399491(k). Classical class "
                    + "terminology supplies the meaning of membership, not a proof of this "
                    + "uniform source-and-order assertion. The proof constructs the cubic "
                    + "endpoint partner, characterizes multiple classes by a norm-D solution "
                    + "whose first coordinate is not divisible by D, and uses integer descent "
                    + "under an explicit norm-one unit to obtain the strict interval. The "
                    + "least-witness principle supplies the full minimum condition.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a399755-pell-class-successor"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name, string title, Formula formula, AssessedProvenance provenance,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(
            DescribeId.Create("a399755-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(FormulaDsl.Disp(formula)),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula DiscriminantFormula()
    {
        var k = Id("k");
        return AllNat(["k"], Equal(
            Call("Discriminant", k), Add(Square(Call("IntOfNat", k)), Num(1))));
    }

    private static Formula SolFormula()
    {
        var k = Id("k");
        var x = Id("x");
        var y = Id("y");
        var d = Call("Discriminant", k);
        return AllNat(["k"], AllInt(["x", "y"], Iff(
            Call("Sol", k, x, y),
            Equal(Subtract(Square(x), Multiply(d, Square(y))), d))));
    }

    private static Formula SameClassFormula()
    {
        var k = Id("k");
        var x = Id("x");
        var y = Id("y");
        var r = Id("r");
        var s = Id("s");
        var u = Id("u");
        var v = Id("v");
        var d = Call("Discriminant", k);
        var unitAction = And(
            Equal(Subtract(Square(u), Multiply(d, Square(v))), Num(1)),
            And(
                Equal(x, Add(Multiply(r, u), Multiply(Multiply(d, s), v))),
                Equal(y, Add(Multiply(r, v), Multiply(s, u)))));
        return AllNat(["k"], AllInt(["x", "y", "r", "s"], Iff(
            Call("SameClass", k, x, y, r, s),
            SomeInt(["u", "v"], unitAction))));
    }

    private static Formula MultipleClassesFormula()
    {
        var k = Id("k");
        var x = Id("x");
        var y = Id("y");
        var r = Id("r");
        var s = Id("s");
        return AllNat(["k"], Iff(
            Call("MultipleClasses", k),
            SomeInt(["x", "y", "r", "s"], And(
                Call("Sol", k, x, y), And(
                    Call("Sol", k, r, s),
                    new Formula.Not(Call("SameClass", k, x, y, r, s)))))));
    }

    private static Formula NextSquarePartnerFormula()
    {
        var k = Id("k");
        var m = Id("m");
        var n = Id("n");
        var minimum = AllNat(["n"], Implies(
            Less(k, n), Implies(SquareCondition(k, n), LessOrEqual(m, n))));
        return AllNat(["k", "m"], Iff(
            Call("NextSquarePartner", k, m),
            And(Less(k, m), And(SquareCondition(k, m), minimum))));
    }

    private static Formula ResultFormula()
    {
        var k = Id("k");
        var m = Id("m");
        var cubic = Add(Multiply(Num(4), new Formula.Power(k, Num(3))), Multiply(Num(3), k));
        return AllNat(["k"], Implies(Less(Num(0), k),
            SomeNat(["m"], And(
                Call("NextSquarePartner", k, m),
                Iff(Less(m, cubic), Call("MultipleClasses", k))))));
    }

    private static Formula SquareCondition(Formula k, Formula m) =>
        Call("IsSquare", Multiply(Add(Square(k), Num(1)), Add(Square(m), Num(1))));

    private static Formula Square(Formula value) => new Formula.Power(value, Num(2));

    private static Formula AllNat(string[] names, Formula body) =>
        Bind(FormulaQuantifier.ForAll, names, Naturals(), body);

    private static Formula SomeNat(string[] names, Formula body) =>
        Bind(FormulaQuantifier.Exists, names, Naturals(), body);

    private static Formula AllInt(string[] names, Formula body) =>
        Bind(FormulaQuantifier.ForAll, names, new Formula.Integers(), body);

    private static Formula SomeInt(string[] names, Formula body) =>
        Bind(FormulaQuantifier.Exists, names, new Formula.Integers(), body);

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Bind(FormulaQuantifier quantifier, string[] names, Formula domain, Formula body) =>
        new Formula.BindMany(quantifier,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
