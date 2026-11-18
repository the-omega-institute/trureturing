using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class SlaterCutPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/SlaterCutPhase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial cuts and fixed-occupation shuffle phases",
        H("Spatial cuts and fixed-occupation shuffle phases"),
        Blocks(
            Paragraph(Text("The sites have a linear order. The retained side is a set of sites and the traced side is its complement. An occupation label on either side specifies a finite set of occupied sites.")),
            Entry("Alternates", "Four alternating sites", Alternation(),
                "Read four strictly increasing sites. Membership in the retained side alternates at each step, starting on either side.",
                DescribeRole.Definition),
            Entry("not_alternates_iff", "One side is an interval", IntervalCriterion(),
                "The cut has no four alternating sites exactly when one side is order connected. Without alternation, a hole between two retained sites forces every traced site between those endpoints. A retained site between two such traced sites would complete an alternating quadruple.",
                DescribeRole.Theorem),
            Entry("crossCount", "Cross-inversion count", CrossCount(),
                "For each occupied retained site the sum counts occupied traced sites to its left. These are exactly the pairs that cross when the retained sites are placed first.",
                DescribeRole.Definition),
            Entry("reduction_charpoly", "Characteristic polynomial of the signed marginal", MarginalSpectrum(),
                "On the total occupation k sector, the sign depends only on the traced occupation if the retained side is an interval. It cancels in the marginal. If the traced side is an interval, the sign on that sector depends only on the retained occupation and gives a diagonal unitary conjugation. An empty side gives sign one. The two Gram matrices have identical characteristic polynomials, including all zero roots with multiplicity.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string title, Formula formula, string explanation, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("slater-cut-phase-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);

    private static Formula Retained => FormulaDsl.Id("I");
    private static Formula Traced => Seq(Retained, Caret, Grp(FormulaDsl.Id("c")));
    private static Formula Operator(string name) => Seq(Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula Parenthesize(Formula value) => Seq(Open, value, Close);
    private static Formula Call(Formula function, Formula argument) => Seq(function, Parenthesize(argument));
    private static Formula Member(string site, Formula side) => Seq(FormulaDsl.Id(site), Sp, InMacro, Sp, side);
    private static Formula Pair(Formula first, Formula second) => Seq(first, Comma, Sp, second);
    private static Formula Typed(Formula name, Formula type) => Seq(name, Colon, Sp, type);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(Operator(name), type), CloseBracket);
    private static Formula Type => Operator("Type");
    private static Formula FiniteSites => Call(Operator("Finset"), Iota);
    private static Formula SiteBinder => Seq(
        Forall, Sp, Typed(Iota, Type), Comma, Sp, Instance("LinearOrder", Iota), Comma, Sp);
    private static Formula CutBinder => Seq(
        SiteBinder, Typed(Retained, Call(Operator("Set"), Iota)), Comma, Sp);
    private static Formula NoAlternation => Seq(Neg, Call(Operator("Alternates"), Retained));

    private static Formula Alternation() => Seq(
        CutBinder, Call(Operator("Alternates"), Retained), Sp, Iff, Sp,
        Exists, Sp, FormulaDsl.Id("x"), Comma, FormulaDsl.Id("y"), Comma, FormulaDsl.Id("z"), Comma, FormulaDsl.Id("w"), Sp, InMacro, Sp, Iota, Comma, Sp,
        FormulaDsl.Id("x"), Lt, FormulaDsl.Id("y"), Lt, FormulaDsl.Id("z"), Lt, FormulaDsl.Id("w"), Sp, Land, Sp,
        Parenthesize(Seq(
            Parenthesize(Seq(Member("x", Retained), Sp, Land, Sp, Member("y", Traced), Sp, Land, Sp,
                Member("z", Retained), Sp, Land, Sp, Member("w", Traced))),
            Sp, Lor, Sp,
            Parenthesize(Seq(Member("x", Traced), Sp, Land, Sp, Member("y", Retained), Sp, Land, Sp,
                Member("z", Traced), Sp, Land, Sp, Member("w", Retained))))));

    private static Formula IntervalCriterion() => Seq(
        CutBinder, NoAlternation, Sp, Iff, Sp,
        Call(Operator("OrdConnected"), Retained), Sp, Lor, Sp, Call(Operator("OrdConnected"), Traced));

    private static Formula CrossCount() => Seq(
        SiteBinder, Typed(Pair(FormulaDsl.Id("a"), FormulaDsl.Id("b")), FiniteSites), Comma, Sp,
        Call(Operator("crossCount"), Pair(FormulaDsl.Id("a"), FormulaDsl.Id("b"))), Sp, Eq, Sp,
        Sum, Underscore, Grp(Member("i", FormulaDsl.Id("a"))),
        Sum, Underscore, Grp(Member("j", FormulaDsl.Id("b"))),
        Seq(Mathbf, Grp(D(1)), Underscore, Grp(FormulaDsl.Id("j"), Lt, FormulaDsl.Id("i"))));

    private static Formula Cardinality(Formula occupation) => Seq(Lvert, Sp, occupation, Sp, Rvert);
    private static Formula Gram(Formula matrix) => Seq(matrix, Sp, matrix, Caret, Grp(Star));
    private static Formula Signed => Seq(Widetilde, Grp(Psi));

    private static Formula MarginalSpectrum()
    {
        var rowType = FormulaDsl.Id("A");
        var columnType = FormulaDsl.Id("B");
        var row = FormulaDsl.Id("x");
        var column = FormulaDsl.Id("y");
        var retainedMap = FormulaDsl.Id("a");
        var tracedMap = FormulaDsl.Id("b");
        var total = FormulaDsl.Id("k");
        var retainedOccupation = Call(retainedMap, row);
        var tracedOccupation = Call(tracedMap, column);
        var entries = Pair(row, column);
        var amplitude = Call(Psi, entries);
        var allRows = Seq(Forall, Sp, row, Sp, InMacro, Sp, rowType, Comma, Sp);
        var allColumns = Seq(Forall, Sp, column, Sp, InMacro, Sp, columnType, Comma, Sp);
        return new Formula.Aligned([
            Seq(CutBinder, Typed(Pair(rowType, columnType), Type), Comma, Sp,
                Instance("Fintype", rowType), Comma, Sp, Instance("DecidableEq", rowType), Comma, Sp,
                Instance("Fintype", columnType), Comma),
            Seq(Typed(retainedMap, Seq(rowType, Sp, To, Sp, FiniteSites)), Comma, Sp,
                Typed(tracedMap, Seq(columnType, Sp, To, Sp, FiniteSites)), Comma, Sp,
                Typed(total, Seq(Mathbb, Grp(FormulaDsl.Id("N")))), Comma, Sp,
                Typed(Psi, Call(Operator("Matrix"), Pair(rowType, Pair(columnType, Seq(Mathbb, Grp(FormulaDsl.Id("C"))))))), Comma),
            Seq(Operator("let"), Sp, Signed, Sp, Eq, Sp, Parenthesize(entries), Sp, Mapsto, Sp,
                Parenthesize(Seq(Minus, D(1))), Caret,
                Grp(Call(Operator("crossCount"), Pair(retainedOccupation, tracedOccupation))), Sp, amplitude, Sp, Operator("in")),
            Seq(NoAlternation, Sp, Land, Sp,
                Parenthesize(Seq(allRows, retainedOccupation, Sp, Subseteq, Sp, Retained)), Sp, Land, Sp,
                Parenthesize(Seq(allColumns, tracedOccupation, Sp, Subseteq, Sp, Traced)), Sp, Land),
            Seq(Parenthesize(Seq(allRows, allColumns, Cardinality(retainedOccupation), Plus,
                Cardinality(tracedOccupation), Sp, Neq, Sp, total, Sp, Longrightarrow, Sp, amplitude, Eq, D(0)))),
            Seq(Longrightarrow, Sp, Call(Operator("charpoly"), Gram(Signed)), Sp, Eq, Sp,
                Call(Operator("charpoly"), Gram(Psi)))
        ]);
    }
}
