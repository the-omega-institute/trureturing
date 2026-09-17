using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SchroederPeakAlternatingQuadraticMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/schulte2017a060693");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's alternating quadratic peak moment for large Schroeder paths.",
        H("Schroeder Paths and the Alternating Quadratic Peak Moment"),
        Blocks(
            Paragraph(Text("A word over U, D, and H is measured horizontally by giving U and D weight one and H weight two. The generator is defined by its first return, and T counts generated words with a prescribed number of adjacent U,D pairs.")),
            Paragraph(Text("All indices are natural numbers. List.count counts occurrences of a step, take selects a prefix, and Fin (n+1) supplies the finite index range. Integer powers and products in the final identity are evaluated in Z.")),
            Node("Step", "The three-step alphabet", StepFormula(),
                "Step consists of the up, down, and horizontal letters U, D, and H.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a060693-inst-fintype-step"),
                DeclarationHandle.Create(Prefix + "instFintypeStep"),
                H("Finite three-step alphabet"),
                StatementSource.FromAuthor(FintypeStepFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The anonymous instance command generates this auto-named declaration. "
                    + "The three-letter Step alphabet is finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a060693-inst-decidable-eq-step"),
                DeclarationHandle.Create(Prefix + "instDecidableEqStep"),
                H("Decidable equality on steps"),
                StatementSource.FromAuthor(DecidableEqStepFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The deriving DecidableEq command generates this auto-named declaration. "
                    + "Equality on the three-letter Step alphabet is decidable."))),
                DescribeRole.Definition),
            Node("stepWeight", "Horizontal step weights", StepWeightFormula(),
                "The up and down letters have horizontal weight one, while the horizontal letter has weight two.",
                DescribeRole.Definition),
            Node("weight", "Word weight", WeightFormula(),
                "The weight of a word is the sum of the horizontal weights of its letters.",
                DescribeRole.Definition),
            Node("PrefixNonnegative", "Prefix nonnegativity", PrefixFormula(),
                "Every prefix has no more down letters than up letters.",
                DescribeRole.Definition),
            Node("schroeder", "The first-return Schroeder generator", SchroederFormula(),
                "The empty word is the zero object. A positive generator word either begins with H and a word of the preceding size, or begins with U, follows a generated inside word, returns with D, and continues with a generated outside word.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("peaks", "Adjacent up-down peaks", PeaksFormula(),
                "peaks counts adjacent occurrences of U followed immediately by D.",
                DescribeRole.Definition),
            Node("T", "The peak-counted triangle", TFormula(),
                "T(n,k) is the cardinality of the generated words of semilength n having k peaks.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SchroederPath", "A generated Schroeder path", PathFormula(),
                "A SchroederPath is a word together with a proof that it belongs to the generator at its semilength.",
                DescribeRole.Definition),
            Node("firstReturnEquiv", "First-return decomposition", FirstReturnFormula(),
                "The equivalence separates a positive path into its initial H case or its U, inside, D, outside first-return case.",
                DescribeRole.Definition),
            Node("first_return_peaks", "Peak preservation under first return", FirstReturnPeaksFormula(),
                "The peak count of a first-return word is the sum of the inner and outer peak counts, with one additional peak exactly when the inner word is empty.",
                DescribeRole.Theorem),
            Node("mem_schroeder_iff", "The generator characterization", MembershipFormula(),
                "This identity connects the recursive generator with the path description: a word is generated exactly when its weight is 2n, its U and D counts agree, and every prefix is nonnegative.",
                DescribeRole.Theorem),
            Node("T_first_return_recurrence", "The peak recurrence", RecurrenceFormula(),
                "The first-return equivalence and finite-fiber counting split T(n+1,k) into the initial H contribution, the empty-inside peak contribution, and the double convolution over nonempty inside indices.",
                DescribeRole.Theorem),
            Node("schulte_a060693", "Schulte's alternating quadratic moment", SchulteFormula(),
                "The zeroth, first, and second falling signed peak moments satisfy the recurrences induced by first return. Their closed forms reduce the alternating quadratic moment to n squared plus n plus one.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a060693-schroeder-peak-alternating-quadratic-moment"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a060693-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula left, Formula right) => Seq(left, Sp, FormulaDsl.Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Steps() => Call("Step");
    private static Formula Words() => Call("List", Steps());
    private static Formula W() => F.Id("w");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula I() => F.Id("i");
    private static Formula U() => F.Id("U");
    private static Formula Dn() => F.Id("D");
    private static Formula Hh() => F.Id("H");
    private static Formula Sum(Formula index, Formula bound, Formula body) =>
        Seq(new Formula.Subscript(FormulaDsl.Sum, Seq(index, Sp, InMacro, Sp, bound)), Sp, body);
    private static Formula Range(Formula upper) => Call("Fin", upper);
    private static Formula Indicator(Formula condition, Formula yes, Formula no) =>
        Call("if", condition, yes, no);

    private static Formula StepFormula() => Disp(Eq(Named("Step"),
        Seq(OpenBrace, U(), Comma, Sp, Dn(), Comma, Sp, Hh(), CloseBrace)));

    private static Formula FintypeStepFormula() =>
        Disp(Parenthesized(Call("Fintype", F.Id("Step"))));

    private static Formula DecidableEqStepFormula() =>
        Disp(Parenthesized(Call("DecidableEq", F.Id("Step"))));

    private static Formula StepWeightFormula() => Disp(new Formula.Aligned([
        Eq(Call("stepWeight", U()), D(1)),
        Eq(Call("stepWeight", Dn()), D(1)),
        Eq(Call("stepWeight", Hh()), D(2))
    ]));

    private static Formula WeightFormula() => Disp(Bound("w", Words(),
        Eq(Call("weight", W()), Call("sum", Call("map", Named("stepWeight"), W())))));

    private static Formula PrefixFormula() => Disp(Bound("w", Words(),
        Seq(Call("PrefixNonnegative", W()), Sp, Iff, Sp,
            Bound("i", Nat(), Seq(Call("count", Dn(), Call("take", I(), W())), Sp,
                Le, Sp, Call("count", U(), Call("take", I(), W())))))));

    private static Formula SchroederFormula()
    {
        Formula inside = Call("image", Seq(Hh(), Sp, Plus, Sp, Dot), Call("schroeder", N()));
        Formula pair = Call("product", Call("schroeder", I()),
            Call("schroeder", Sub(N(), I())));
        Formula branch = Call("image",
            Seq(Open, F.Id("q"), Comma, Sp, F.Id("p"), Close, Sp, Mapsto, Sp,
                U(), Sp, Plus, Sp, F.Id("q"), Sp, Plus, Sp, Dn(), Sp, Plus, Sp, F.Id("p")), pair);
        Formula indexed = Call("biUnion",
            Seq(I(), Sp, InMacro, Sp, Range(Add(N(), D(1)))), branch);
        return Disp(new Formula.Aligned([
            Eq(Call("schroeder", D(0)), Seq(OpenBrace, Open, Close, CloseBrace)),
            Eq(Call("schroeder", Add(N(), D(1))), Call("union", inside, indexed))
        ]));
    }

    private static Formula PeaksFormula() => Disp(new Formula.Aligned([
        Eq(Call("peaks", Seq(OpenBracket, CloseBracket)), D(0)),
        Eq(Call("peaks", Seq(OpenBracket, F.Id("a"), CloseBracket)), D(0)),
        Eq(Call("peaks", Seq(F.Id("a"), Sp, Plus, Sp, F.Id("b"), Sp, Plus, Sp, F.Id("r"))),
            Add(Indicator(Seq(F.Id("a"), Sp, FormulaDsl.Eq, Sp, U(), Sp, Land, Sp,
                    F.Id("b"), Sp, FormulaDsl.Eq, Sp, Dn()), D(1), D(0)),
                Call("peaks", Seq(F.Id("b"), Sp, Plus, Sp, F.Id("r")))))
    ]));

    private static Formula TFormula() => Disp(Bound("n", Nat(), Bound("k", Nat(),
        Eq(Call("T", N(), K()), Call("card", Call("filter",
            Seq(F.Id("w"), Sp, Mapsto, Sp, Eq(Call("peaks", W()), K())),
            Call("schroeder", N())))))));

    private static Formula PathFormula() => Disp(Bound("n", Nat(),
        Eq(Call("SchroederPath", N()), Call("Subtype", Words(),
            Seq(W(), Sp, Mapsto, Sp, W(), Sp, InMacro, Sp, Call("schroeder", N()))))));

    private static Formula FirstReturnFormula() => Disp(Bound("n", Nat(),
        Seq(Call("firstReturnEquiv", N()), Sp, FormulaDsl.Colon, Sp,
            Call("Equiv", Call("SchroederPath", Add(N(), D(1))),
                Call("Sum", Call("SchroederPath", N()),
                    Call("Sigma", Seq(I(), Sp, InMacro, Sp, Call("Fin", Add(N(), D(1)))),
                        Call("Product", Call("SchroederPath", I()),
                            Call("SchroederPath", Sub(N(), I())))))))));

    private static Formula FirstReturnPeaksFormula() => Disp(Bound("i", Nat(), Bound("n", Nat(),
        Bound("q", Words(), Bound("p", Words(),
            Seq(F.Id("q"), Sp, InMacro, Sp, Call("schroeder", I()), Sp, Rightarrow, Sp,
                F.Id("p"), Sp, InMacro, Sp, Call("schroeder", N()), Sp, Rightarrow, Sp,
                Eq(Call("peaks", Seq(U(), Sp, Plus, Sp, F.Id("q"), Sp, Plus, Sp, Dn(), Sp,
                        Plus, Sp, F.Id("p"))),
                    Add(Add(Call("peaks", F.Id("q")), Call("peaks", F.Id("p"))),
                        Indicator(Seq(I(), Sp, FormulaDsl.Eq, Sp, D(0)), D(1), D(0))))))))));

    private static Formula MembershipFormula() => Disp(Bound("n", Nat(), Bound("w", Words(),
        Seq(Call("mem", W(), Call("schroeder", N())), Sp, Iff, Sp, Parenthesized(Seq(
            Eq(Call("weight", W()), Mul(D(2), N())), Sp, Land, Sp,
            Eq(Call("count", U(), W()), Call("count", Dn(), W())), Sp, Land, Sp,
            Call("PrefixNonnegative", W())))))));

    private static Formula RecurrenceFormula() => Disp(Bound("n", Nat(), Bound("k", Nat(),
        Eq(Call("T", Add(N(), D(1)), K()),
            Add(Add(Call("T", N(), K()),
                Indicator(Seq(D(0), Sp, Lt, Sp, K()), Call("T", N(), Sub(K(), D(1))), D(0))),
                Sum(I(), Range(N()), Sum(F.Id("j"), Range(Add(K(), D(1))),
                    Mul(Call("T", Add(I(), D(1)), F.Id("j")),
                        Call("T", Sub(N(), Add(I(), D(1))), Sub(K(), F.Id("j")))))))))));

    private static Formula SchulteFormula()
    {
        Formula term = Mul(Mul(Pow(new Formula.Negate(D(1)), K()), Call("T", N(), K())),
            Pow(Sub(Add(N(), D(1)), K()), D(2)));
        Formula sum = Sum(K(), Range(Add(N(), D(1))), term);
        return Disp(Bound("n", Nat(), Eq(sum, Add(Add(Pow(N(), D(2)), N()), D(1)))));
    }
}
