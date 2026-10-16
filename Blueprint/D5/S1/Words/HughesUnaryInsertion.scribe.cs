using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class HughesUnaryInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/HughesUnaryInsertion.";
    private static readonly LibraryNoteRef Hughes = LibraryNoteRef.Create("D5/L/Words/hughes2026a27755");
    private static readonly Formula A = F.Id("a"), C = F.Id("cs"), Hs = F.Id("h");
    private static readonly Formula E = F.Id("e"), W = F.Id("w"), M = F.Id("M");
    private static Formula Words => Call("List", F.Id("alpha"));
    private static Formula Masses => Call("List", Call("Nat"));
    private static Formula Masks => Call("List", F.Id("Side"));
    private static Formula Gap(Formula h) => Call("gap", A, C, h);
    private static Formula SumMass => Call("zipWith", F.Id("add"), Hs, E);
    private static Formula Unary => Call("replicate", F.Id("m"), A);
    private static Formula Cost(bool reverse) => reverse ? Add(Num(1), Call("internalOccupied", E)) : Call("occupied", E);
    private static Formula Left(bool reverse) => reverse ? Gap(Hs) : Unary;
    private static Formula Right(bool reverse) => reverse ? Unary : Gap(Hs);
    private static Formula Away => All("c", F.Id("alpha"), Implies(Member(F.Id("c"), C), NotEqual(F.Id("c"), A)));
    private static Formula Lengths => Equal(Call("length", Hs), Add(Call("length", C), Num(1)));
    private static Formula Assumptions => And(Away, And(Lengths,
        And(Equal(Call("length", E), Call("length", Hs)), Equal(Call("sum", E), F.Id("m")))));
    private static Formula BindPresentation(Formula body) => All("alpha", Call("Type"),
        All("a", F.Id("alpha"), All("m", Call("Nat"), All("cs", Words, All("h", Masses, body)))));
    private static Formula Bind(Formula body) => BindPresentation(All("e", Masses, body));
    private static Formula BindTrace(Formula body) => All("alpha", Call("Type"),
        All("a", F.Id("alpha"), All("cs", Words, All("h", Masses,
            All("e", Masses, All("w", Words, All("M", Masks, body)))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gap masses identify native unary insertion minima in both ordered orientations.",
        H("Unary and Reverse-Unary Native Insertion"), Blocks(
            Paragraph(Text("Words and masks use the original ordered source schedule: the first "
                + "source is inserted and the second is the base. The degree is the minimum "
                + "number of maximal nonempty first-source runs over all actual masks, with "
                + "infinity for an invalid output. Neither source roles nor minimum semantics "
                + "are exchanged when passing to the reverse-unary case.")),
            Paragraph(Text("The inserted-unary gap, degree and spectrum arguments use Hughes "
                + "arXiv v2, Section 11, Theorem 9: https://arxiv.org/abs/2608.27755v2. "
                + "The reverse-unary and universal minimum-mask exchange statements are "
                + "separate arguments.")),
            Node("occupied", "Occupied extra gaps", Disp(All("e", Masses,
                Equal(Call("occupied", E), Call("countPositive", E)))),
                "Count strictly positive extra masses; a positive original gap with zero extra "
                + "mass is unoccupied. Both outer gaps are included in this count.", false, false),
            Node("internalOccupied", "Occupied internal extra gaps", Disp(All("e", Masses,
                Equal(Call("internalOccupied", E), Call("occupied", Call("dropLast", Call("tail", E)))))),
                "Discard the initial and terminal gap before counting. For zero or one "
                + "non-a occurrences there are no internal gaps.", false, false),
            Node("Sh", "Actual native shuffles", Disp(All("alpha", Call("Type"),
                All("u", Words, All("v", Words, All("w", Words,
                    Iff(Member(W, Call("Sh", F.Id("u"), F.Id("v"))),
                        Ex("M", Masks, Call("ValidMask", F.Id("u"), F.Id("v"), W, M)))))))),
                "Membership means an actual positional mask evaluates to the word and consumes "
                + "both original sources. No separate ordinary-shuffle identification is used.", false, false),
            Node("spectrum", "Attained natural degrees", Disp(All("alpha", Call("Type"),
                All("u", Words, All("v", Words, All("r", Call("Nat"),
                    Iff(Member(F.Id("r"), Call("spectrum", F.Id("u"), F.Id("v"))),
                        Ex("w", Words, And(Member(W, Call("Sh", F.Id("u"), F.Id("v"))),
                            Equal(Call("degree", F.Id("u"), F.Id("v"), W), F.Id("r")))))))))),
                "A natural value occurs only through an actual shuffle output with that "
                + "native minimum; infinity contributes no natural spectrum value.", false, false),
            Node("inserted_gap_iff", "Inserted-unary unique gap masses", GapFormula(false),
                "Non-a occurrences are forced to the base source. Every output has a unique "
                + "nonnegative extra vector of total inserted length, and every such vector "
                + "has a full native mask. Repeated separator letters remain indexed occurrences.", true, true),
            Node("reverse_gap_iff", "Reverse-unary unique gap masses", GapFormula(true),
                "Here non-a occurrences are forced to the inserted source. The same "
                + "concatenation description retains all base mass, including both outer gaps.", true, false),
            Node("inserted_degree", "Inserted-unary minimum and attainment", DegreeFormula(false),
                "Each occupied gap needs an inserted run because non-a letters separate gaps. "
                + "The grouped mask puts each gap's inserted letters together, reaches exactly "
                + "that number of runs, and preserves both projections. This formalizes the "
                + "occupied-gap proof of Hughes arXiv v2, Theorem 9, for arbitrary alphabets. For positive "
                + "inserted length its convention agrees with native U-run degree; when that "
                + "length is zero the native count is zero.", true, true),
            Node("reverse_degree", "Reverse-unary internal minimum and attainment", DegreeFormula(true),
                "With at least one non-a occurrence, every occupied internal gap separates "
                + "forced inserted-source groups. The grouped construction places outer base "
                + "material outside those groups, so the count is one plus occupied internal "
                + "gaps. Original a copies in every gap remain part of the inserted projection.", true, false),
            Node("reverse_degree_all", "Reverse-unary boundary cases", Bind(Implies(
                And(Assumptions, NotEqual(Gap(Hs), F.Id("nil"))), Equal(
                    Call("degree", Gap(Hs), Unary, Gap(SumMass)),
                    Call("ite", Equal(C, F.Id("nil")), Num(1), Cost(true))))),
                "For no non-a occurrences, nonemptiness of the inserted source forces a "
                + "positive unary length and the degree is one. With a single non-a occurrence "
                + "there are no internal gaps, again giving degree one regardless of both "
                + "outer extra masses. Both statements use the same actual source projections.", true, false),
            Node("inserted_trace_lower", "Every-mask inserted lower bound", TraceLower(false),
                "Non-a base occurrences separate the label lists of successive gaps. Each "
                + "positive first-source count contributes at least one maximal U-run.", true, false),
            Node("reverse_trace_lower", "Every-mask reverse lower bound", TraceLower(true),
                "The first non-a occurrence forces an initial U-group. Every positive "
                + "internal base count forces a further separator; exterior counts add none.", true, false),
            Node("inserted_spectrum", "Full inserted-unary spectrum", SpectrumFormula(false),
                "The spectrum is every integer from one to min(m, length(cs)+1), for m>0. "
                + "Support is bounded by both total mass and gap count. To attain r, put one "
                + "unit in r-1 gaps, the remaining positive mass in one gap, and zero elsewhere.", true, true),
            Node("reverse_spectrum", "Full reverse-unary spectrum", SpectrumFormula(true),
                "For a nonempty inserted source the spectrum is every integer from one to "
                + "1+min(n, length(cs)-1), with truncated subtraction. Put one unit in each "
                + "chosen internal gap and all remaining mass at an exterior end. For no "
                + "non-a occurrences the only value is one.", true, false),
            Node("InsertedTight", "Equality in every inserted gap", ShapeFormula(false, false),
                "This positional trace requires rho(b)=1 in each gap whose inserted count "
                + "is positive, and rho(b)=0 otherwise. All non-a occurrences have label V. "
                + "Thus each occupied indexed gap has exactly one whole U-run.", false, false),
            Node("ReverseTailTight", "Internal and terminal equality", ShapeFormula(true, true),
                "An internal label gap has the form U^x V^e U^z, with all its base mass e "
                + "in that single V-block. The terminal gap has form U^x V^y. The internal "
                + "restart cost is one exactly when e>0, and the terminal restart cost is zero.", false, false),
            Node("ReverseTight", "Full reverse minimum structure", ShapeFormula(true, false),
                "The initial gap is V^x U^y followed by its forced non-a U occurrence, and "
                + "the remaining trace has the internal and terminal forms above. Every "
                + "U segment attaches to a bounding non-a occurrence; there is no additional "
                + "all-a U-run. Outer base material is retained in its actual position.", false, false),
            Node("inserted_minimum_shape", "Every inserted-unary minimum mask", MinimumShape(false),
                "Comparison with the grouped attaining mask forces equality in each "
                + "individual gap lower bound, for every minimum mask of the output.", true, false),
            Node("reverse_minimum_shape", "Every reverse-unary minimum mask", MinimumShape(true),
                "With at least one non-a occurrence, equality forces the initial cost one "
                + "and every internal and terminal cost to be tight. The binary label "
                + "classification proves the displayed pure-block forms for every minimum mask.", true, false),
            Node("spectra", "Spectra of arbitrary actual source words", ActualSpectra(),
                "For arbitrary nonempty u,v and positive m,n, let s_a(x) be the number of "
                + "non-a occurrences of the actual word x, counting repetitions. Then "
                + "D(a^m,v)={r: 1<=r<=min(m,s_a(v)+1)} and "
                + "D(u,a^n)={r: 1<=r<=1+min(n,s_a(u)-1)}. The occurrence count is recovered "
                + "from the canonical presentation of each actual source word.", true, false))));

    private static Formula ActualSpectra()
    {
        Formula u = F.Id("u"), v = F.Id("v"), r = F.Id("r");
        Formula interval(Formula bound) => And(Le(Num(1), r), Le(r, bound));
        Formula first = All("r", Call("Nat"), Iff(Member(r, Call("spectrum", Unary, v)),
            interval(Call("min", F.Id("m"), Add(Call("length", Call("spine", A, v)), Num(1))))));
        Formula second = All("r", Call("Nat"), Iff(Member(r,
            Call("spectrum", u, Call("replicate", F.Id("n"), A))),
            interval(Add(Num(1), Call("min", F.Id("n"),
                Subtract(Call("length", Call("spine", A, u)), Num(1)))))));
        Formula assumptions = And(NotEqual(u, F.Id("nil")), And(NotEqual(v, F.Id("nil")),
            And(Le(Num(1), F.Id("m")), Le(Num(1), F.Id("n")))));
        return All("alpha", Call("Type"), All("a", F.Id("alpha"), All("m", Call("Nat"),
            All("n", Call("Nat"), All("u", Words, All("v", Words,
                Implies(assumptions, And(first, second))))))));
    }

    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula TraceLower(bool reverse) => BindTrace(
        Implies(reverse ? And(Call("Trace", A, F.Id("first"), C, Hs, E, W, M), NotEqual(C, F.Id("nil")))
            : Call("Trace", A, F.Id("second"), C, Hs, E, W, M), Le(Cost(reverse), Call("rho", M))));
    private static Formula ShapeFormula(bool reverse, bool tail) => BindTrace(Seq(
        Call(reverse ? (tail ? "ReverseTailTight" : "ReverseTight") : "InsertedTight", A, C, Hs, E, W, M),
        Sp, Colon, Sp, Call("Prop")));
    private static Formula MinimumShape(bool reverse) => Bind(All("w", Words, All("M", Masks,
        All("r", Call("Nat"), Implies(And(reverse ? And(Assumptions, NotEqual(C, F.Id("nil"))) : Assumptions,
            And(Equal(W, Gap(SumMass)), Call("IsMinimumMask", Left(reverse), Right(reverse), W, M, F.Id("r")))),
            Call(reverse ? "ReverseTight" : "InsertedTight", A, C, Hs, E, W, M))))));
    private static Formula SpectrumFormula(bool reverse) => All("alpha", Call("Type"), All("a", F.Id("alpha"),
        All("m", Call("Nat"), All("cs", Words, All("h", Masses, Implies(
            And(Away, And(Lengths, reverse ? NotEqual(Gap(Hs), F.Id("nil")) : Le(Num(1), F.Id("m")))),
            All("r", Call("Nat"), Iff(Member(F.Id("r"), Call("spectrum", Left(reverse), Right(reverse))),
                And(Le(Num(1), F.Id("r")), Le(F.Id("r"), reverse ? Add(Num(1), Call("min", F.Id("m"),
                    Call("NatSub", Call("length", C), Num(1)))) : Call("min", F.Id("m"), Add(Call("length", C), Num(1)))))))))))));

    private static Formula GapFormula(bool reverse)
    {
        Formula valid(Formula e) => And(Equal(Call("length", e), Call("length", Hs)),
            And(Equal(Call("sum", e), F.Id("m")), Equal(W, Gap(Call("zipWith", F.Id("add"), Hs, e)))));
        return BindPresentation(All("w", Words, Implies(And(Away, Lengths),
            Iff(Member(W, Call("Sh", Left(reverse), Right(reverse))),
                Ex("e", Masses, And(valid(E), All("f", Masses,
                    Implies(valid(F.Id("f")), Equal(F.Id("f"), E)))))))));
    }

    private static Formula DegreeFormula(bool reverse)
    {
        Formula assumptions = reverse ? And(Assumptions, NotEqual(C, F.Id("nil"))) : Assumptions;
        Formula cost = Cost(reverse);
        Formula minimum = Call("IsMinimumMask", Left(reverse), Right(reverse), Gap(SumMass),
            Call("grouped", F.Id(reverse ? "first" : "second"), C, Hs, E), cost);
        return Disp(Bind(Implies(assumptions, And(minimum,
            Equal(Call("degree", Left(reverse), Right(reverse), Gap(SumMass)), cost)))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool theorem, bool literature) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Hughes) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Ex(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
