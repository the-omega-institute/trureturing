using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class DucciModularCycleFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/DucciModularCycleFactorization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/fellman2023ducci");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every cycle of the modular multiplicative Ducci game factors through one constant and "
            + "two generator cycles.",
        H("Factoring the Cycles of the Modular Multiplicative Ducci Game"),
        Blocks(
            Node("step-definition", "One move of the game", "step",
                StepFormula(),
                "The source replaces the difference map of the classical four-number game by a "
                    + "product map: every corner of the square is replaced by its product with "
                    + "the next corner. Corners are indexed by the residues modulo four, so that "
                    + "the next corner is addition of one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("in-cycle-definition", "Lying on a cycle", "InCycle",
                InCycleFormula(),
                "The source says a 4-tuple is in a cycle when iterating the game some positive "
                    + "number of times returns a 4-tuple equivalent to it under the symmetries "
                    + "of the square. That condition is the same as returning the 4-tuple "
                    + "itself. Rotations commute with the map, so a rotation after L moves gives "
                    + "the identity after four times L moves. For a reflection the map conjugates "
                    + "to the reflection shifted by one corner, so two rounds of L moves give a "
                    + "rotation and eight rounds give the identity. The displayed form is the "
                    + "one used below.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("const-definition", "The 4-tuple with four equal entries", "const",
                ConstFormula(),
                "The 4-tuple carrying one value at all four corners.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("constant-cycle-definition", "Constant cycles", "InConstantCycle",
                ConstantCycleFormula(),
                "The source calls a cycle constant when all of its 4-tuples have equal entries, "
                    + "and its Lemma 3 shows that one such 4-tuple forces all of them.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generator-definition", "Generator 4-tuples", "gen",
                GenFormula(),
                "The source calls a 4-tuple of this shape, with x invertible modulo n, a "
                    + "generator 4-tuple whenever it lies on a cycle.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generator-cycle-definition", "Generator cycles", "InGeneratorCycle",
                GeneratorCycleFormula(),
                "The source calls a cycle containing a generator 4-tuple a generator cycle, and "
                    + "notes that every second 4-tuple on such a cycle is again a generator "
                    + "4-tuple.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("product-definition", "Corner-by-corner product", "prod3",
                Prod3Formula(),
                "The source multiplies 4-tuples entry by entry, and a product of cycles is the "
                    + "cycle carrying the products of their 4-tuples.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-statement", "The factorization of cocomposite cycles", "claim",
                ClaimFormula(),
                "Conjecture 1 of the source reads verbatim: \"Every cocomposite cycle is a "
                    + "product of a constant cycle and two generating cycles.\" It is followed "
                    + "by: \"This conjecture has been verified for all moduli up to 161. One "
                    + "possible direction of proving this conjecture is to show that all "
                    + "cocomposite cycles are a product of a cocomposite constant cycle and a "
                    + "coprime cycle, but we have been unsuccessful on this front.\" By Lemma 2 "
                    + "of the source a cycle has either all entries invertible or none, and the "
                    + "second case is the cocomposite one displayed here.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-proved", "The factorization holds", "result",
                ResultFormula(),
                "The hypothesis that the entries are not invertible is never used, so the same "
                    + "construction covers coprime cycles and reproves Theorem 13 of the source, "
                    + "whose own argument inverts entries and therefore applies only to the "
                    + "coprime case. Write Q for the product of the four entries of a 4-tuple on "
                    + "a cycle of length L. The product of the four entries squares at every "
                    + "move, so Q is its own power with exponent two to the L. The second move "
                    + "carries opposite corners to Q, which gives both that the product of the "
                    + "entries at corners zero and two equals the product at corners one and "
                    + "three, and that this common value is Q raised to two to the L minus one. "
                    + "The third move has exponent vector one, three, three, one at every "
                    + "corner, so Q divides every entry. The fourth move has exponent vector "
                    + "two, four, six, four, so every entry after it is a square, and therefore "
                    + "every entry of the 4-tuple is a power with exponent two to the k for "
                    + "every k. Two of the iterated squaring maps of the finite ring of residues "
                    + "agree, and the gap t between them gives one exponent with the property "
                    + "that raising any such entry to the power two to the t returns it. Put D "
                    + "one less than two to the t, and let the idempotent be Q raised to D; it "
                    + "absorbs every positive power of Q and every entry. The constant factor is "
                    + "Q raised to two to the L minus two, whose square is the common product of "
                    + "opposite entries. Adding one minus the idempotent to a multiple of the "
                    + "inverse of that constant factor produces genuine units, because the cross "
                    + "terms vanish, and the two generator cycles are built from them. The "
                    + "constant factor returns after t moves; four moves send a generator "
                    + "4-tuple to the generator 4-tuple of the inverse fourth power, so eight "
                    + "moves raise the unit to the sixteenth power and the generator cycle "
                    + "returns after eight t moves. The third factor is the second turned by one "
                    + "corner, the move commutes with that turn, and two moves place it on a "
                    + "generator 4-tuple. Neither a splitting of the ring into prime power parts "
                    + "nor any counting of multiplicative orders enters the argument.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ducci-modular-cycle-factorization"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Tuple() => F.Id("u");
    private static Formula Corner() => F.Id("i");
    private static Formula At(Formula f, Formula i) => Call("entry", f, i);
    private static Formula Iter(Formula m, Formula f) => Call("iterate", m, f);

    private static Formula StepFormula()
    {
        var u = Tuple();
        var i = Corner();
        var body = Equal(At(Call("step", u), i),
            Multiply(At(u, i), At(u, Add(i, D(1)))));
        return Disp(Universal("u", Positions(), Universal("i", Corners(), body)));
    }

    private static Formula InCycleFormula()
    {
        var u = Tuple();
        var l = F.Id("L");
        var inner = And(Less(D(0), l), Equal(Iter(l, u), u));
        var body = Exists("L", Naturals(), inner);
        return Disp(Universal("u", Positions(), Iff(Call("InCycle", u), body)));
    }

    private static Formula ConstFormula()
    {
        var a = F.Id("a");
        var i = Corner();
        return Disp(Universal("a", Residues(),
            Universal("i", Corners(), Equal(At(Call("const", a), i), a))));
    }

    private static Formula ConstantCycleFormula()
    {
        var u = Tuple();
        var m = F.Id("m");
        var a = F.Id("a");
        var tail = Universal("m", Naturals(),
            Exists("a", Residues(), Equal(Iter(m, u), Call("const", a))));
        var body = And(Call("InCycle", u), tail);
        return Disp(Universal("u", Positions(),
            Iff(Call("InConstantCycle", u), body)));
    }

    private static Formula GenFormula()
    {
        var x = F.Id("x");
        var g = Call("gen", x);
        var e0 = Equal(At(g, D(0)), D(1));
        var e1 = Equal(At(g, D(1)), x);
        var e2 = Equal(At(g, D(2)), D(1));
        var e3 = Equal(At(g, D(3)), Call("inverse", x));
        return Disp(Universal("x", Units(), Seq(e0, Sp, Sp, Sp, e1, Sp, Sp, Sp,
            e2, Sp, Sp, Sp, e3)));
    }

    private static Formula GeneratorCycleFormula()
    {
        var u = Tuple();
        var m = F.Id("m");
        var x = F.Id("x");
        var tail = Exists("m", Naturals(),
            Exists("x", Units(), Equal(Iter(m, u), Call("gen", x))));
        var body = And(Call("InCycle", u), tail);
        return Disp(Universal("u", Positions(),
            Iff(Call("InGeneratorCycle", u), body)));
    }

    private static Formula Prod3Formula()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var c = F.Id("C");
        var i = Corner();
        var body = Equal(At(Call("prod3", a, b, c), i),
            Multiply(Multiply(At(a, i), At(b, i)), At(c, i)));
        return Disp(Universal("A", Positions(), Universal("B", Positions(),
            Universal("C", Positions(), Universal("i", Corners(), body)))));
    }

    private static Formula ClaimFormula()
    {
        var u = Tuple();
        var i = Corner();
        var a = F.Id("A");
        var b = F.Id("B");
        var c = F.Id("C");
        var factors = And(Call("InConstantCycle", a),
            And(Call("InGeneratorCycle", b), Call("InGeneratorCycle", c)));
        var target = And(factors, Equal(u, Call("prod3", a, b, c)));
        var witness = Exists("A", Positions(), Exists("B", Positions(),
            Exists("C", Positions(), target)));
        var cocomposite = Universal("i", Corners(),
            new Formula.Not(Call("IsUnit", At(u, i))));
        var inner = Implies(Call("InCycle", u), Implies(cocomposite, witness));
        var over = Universal("u", Positions(), inner);
        var body = Universal("n", Naturals(), Implies(LessEqual(D(2), F.Id("n")), over));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Residues() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Zn"));

    private static Formula Units() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("ZnUnits"));

    private static Formula Corners() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Corner"));

    private static Formula Positions() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Position"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
