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
                "The cut has no four alternating sites exactly when one side is order connected. A hole between two retained sites forces every traced site between those endpoints. A retained site between two such traced sites would complete an alternating quadruple.",
                DescribeRole.Theorem),
            Entry("crossCount", "Cross-inversion count", CrossCount(),
                "For each occupied retained site the sum counts occupied traced sites to its left. These are exactly the pairs that cross when the retained sites are placed first.",
                DescribeRole.Definition),
            Entry("reduction_charpoly", "Characteristic polynomial of the signed marginal", MarginalSpectrum(),
                "The row and column label types A and B are finite, and A has decidable equality. The maps a and b assign finite occupied sets to these labels. The complex amplitude matrix is supported on total occupation k, a natural number. When the retained side is an interval, the sign depends only on the traced occupation and cancels in the marginal. When the traced side is an interval, the sign depends only on the retained occupation and gives a diagonal unitary conjugation. An empty side gives sign one. The two Gram matrices thus have identical characteristic polynomials, including all zero roots with multiplicity.",
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

    private static Formula Alternation() => Seq(
        Call(Operator("Alternates"), Retained), Sp, Iff, Sp,
        Exists, Sp, FormulaDsl.Id("x"), Comma, FormulaDsl.Id("y"), Comma, FormulaDsl.Id("z"), Comma, FormulaDsl.Id("w"), Sp, InMacro, Sp, Iota, Comma, Sp,
        FormulaDsl.Id("x"), Lt, FormulaDsl.Id("y"), Lt, FormulaDsl.Id("z"), Lt, FormulaDsl.Id("w"), Sp, Land, Sp,
        Parenthesize(Seq(
            Parenthesize(Seq(Member("x", Retained), Sp, Land, Sp, Member("y", Traced), Sp, Land, Sp,
                Member("z", Retained), Sp, Land, Sp, Member("w", Traced))),
            Sp, Lor, Sp,
            Parenthesize(Seq(Member("x", Traced), Sp, Land, Sp, Member("y", Retained), Sp, Land, Sp,
                Member("z", Traced), Sp, Land, Sp, Member("w", Retained))))));

    private static Formula IntervalCriterion() => Seq(
        Forall, Sp, Retained, Sp, Subseteq, Sp, Iota, Comma, Sp,
        Neg, Call(Operator("Alternates"), Retained), Sp, Iff, Sp,
        Call(Operator("OrdConnected"), Retained), Sp, Lor, Sp, Call(Operator("OrdConnected"), Traced));

    private static Formula CrossCount() => Seq(
        Call(Operator("crossCount"), Pair(FormulaDsl.Id("a"), FormulaDsl.Id("b"))), Sp, Eq, Sp,
        Sum, Underscore, Grp(Member("i", FormulaDsl.Id("a"))),
        Sum, Underscore, Grp(Member("j", FormulaDsl.Id("b"))),
        Seq(Mathbf, Grp(D(1)), Underscore, Grp(FormulaDsl.Id("j"), Lt, FormulaDsl.Id("i"))));

    private static Formula Cardinality(Formula occupation) => Seq(Lvert, Sp, occupation, Sp, Rvert);
    private static Formula Gram(Formula matrix) => Seq(matrix, Sp, matrix, Caret, Grp(Star));
    private static Formula Signed => Seq(Widetilde, Grp(Psi));

    private static Formula MarginalSpectrum()
    {
        var retainedOccupation = Call(FormulaDsl.Id("a"), FormulaDsl.Id("x"));
        var tracedOccupation = Call(FormulaDsl.Id("b"), FormulaDsl.Id("y"));
        var amplitudes = Call(Psi, Pair(FormulaDsl.Id("x"), FormulaDsl.Id("y")));
        return new Formula.Aligned([
            Seq(Neg, Call(Operator("Alternates"), Retained), Comma, Quad,
                Forall, Sp, FormulaDsl.Id("x"), Sp, InMacro, Sp, FormulaDsl.Id("A"), Comma, Sp, retainedOccupation, Sp, Subseteq, Sp, Retained, Comma, Quad,
                Forall, Sp, FormulaDsl.Id("y"), Sp, InMacro, Sp, FormulaDsl.Id("B"), Comma, Sp, tracedOccupation, Sp, Subseteq, Sp, Traced),
            Seq(Forall, Sp, FormulaDsl.Id("x"), Comma, FormulaDsl.Id("y"), Comma, Sp, Cardinality(retainedOccupation), Plus,
                Cardinality(tracedOccupation), Sp, Neq, Sp, FormulaDsl.Id("k"), Sp, Longrightarrow, Sp, amplitudes, Eq, D(0)),
            Seq(Call(Signed, Pair(FormulaDsl.Id("x"), FormulaDsl.Id("y"))), Eq,
                Parenthesize(Seq(Minus, D(1))), Caret,
                Grp(Call(Operator("crossCount"), Pair(retainedOccupation, tracedOccupation))), Sp, amplitudes),
            Seq(Longrightarrow, Sp, Call(Operator("charpoly"), Gram(Signed)), Sp, Eq, Sp,
                Call(Operator("charpoly"), Gram(Psi)))
        ]);
    }
}
