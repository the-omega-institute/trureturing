using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233255ShapeSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.";
    private const string LiteralPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical proper boundaries preserve every completed-scanner continuation height.",
        H("Relabelling complementary pairs after both distinguished colours appear"),
        Blocks(
            Paragraph(Text("When colours one and two have both appeared, every pair-label cell has "
                + "two individual-colour lifts. A seven-cell row therefore has multiplicity 128. "
                + "Permuting all three pair labels preserves each horizontal and antidiagonal inequality, "
                + "so the entire continuation transfer respects that permutation at every height.")),
            Fact("full_cell", "A fully seen scanner at one cell",
                All("q", Call("Fin", Num(3)), And(
                    Equal(Call(LiteralPrefix + "labelAdvance", FullySeen(), F.Id("q")), FullySeen()),
                    Equal(Call(LiteralPrefix + "labelWeight", FullySeen(), F.Id("q")),
                        Typed(Num(2), Q("Int"))))),
                "For every pair label, both seen flags remain true and the integer lift weight is two."),
            Fact("full_row", "A fully seen scanner along any finite row",
                All("k", Q("Nat"), All("q",
                    new Formula.TypeArrow(Call("Fin", F.Id("k")), Call("Fin", Num(3))), And(
                        Equal(Call(LiteralPrefix + "rowFinish", FullySeen(), F.Id("q")), FullySeen()),
                        Equal(Call(LiteralPrefix + "rowWeight", FullySeen(), F.Id("q")),
                            new Formula.Power(Typed(Num(2), Q("Int")), F.Id("k")))))),
                "For every natural row length and every row of pair labels, both seen flags remain "
                + "true and the integer lift weight is two to that length, including the empty row."),
            Node("proper", "Proper six-cell boundaries", "Adjacent labels differ.", DescribeRole.Definition),
            Node("Shape", "Canonical boundary representatives", "A proper six-cell word whose first two labels are zero and one.",
                DescribeRole.Definition),
            Node("canonical", "Canonical relabelling", "The first label becomes zero, the second becomes one, and the "
                + "remaining label becomes two. Properness makes the first two labels distinct.", DescribeRole.Definition),
            Node("completed_canonical_bridge", "All-height canonical correspondence", "Induction on continuation "
                + "height reindexes actual compatible pair rows by the same label permutation. The completed-scanner "
                + "continuation count therefore depends only on the canonical boundary. The initial and unfinished "
                + "scanner sectors still require their own weighted aggregation.", DescribeRole.Theorem),
            Node("representatives", "Sixteen actual canonical boundaries", "The explicit list contains every proper "
                + "six-cell boundary beginning zero, one, exactly once.", DescribeRole.Definition),
            Node("normalize", "Boundary label normalization", "For any six-cell boundary p, a label equal to p(0) "
                + "becomes zero; otherwise a label equal to p(1) becomes one; every remaining label becomes two. "
                + "The first test takes precedence even when the first two labels coincide. "
                + "Proper boundaries have distinct first two labels.", DescribeRole.Definition),
            Node("shapeEquiv", "Complete boundary enumeration", "A proved equivalence identifies the sixteen indices "
                + "with the actual canonical-boundary subtype, including representatives missing the third label.", DescribeRole.Definition),
            Node("classOf", "Successor class", "For any six-cell boundary, normalize its labels, then test "
                + "representatives zero through fourteen in order, returning the first matching index or "
                + "fifteen if none matches. For a proper boundary, the normalized word has a unique matching "
                + "representative among all sixteen, and this lookup returns its index. For a nonproper "
                + "boundary, the fallback need not identify a matching representative.", DescribeRole.Definition),
            Node("K", "Actual compatible-row matrix", "Entry i,j counts proper seven-cell pair rows compatible "
                + "with representative i whose six-cell suffix has canonical class j.", DescribeRole.Definition),
            Node("F", "Completed-scanner vector", "At height m this is 128 to the power m times K to the power m "
                + "applied to the all-ones vector.", DescribeRole.Definition),
            Node("completed_transfer_bridge", "Exact completed-state matrix powers", "For every natural continuation "
                + "height and every proper labelled six-cell boundary, the original completed-scanner continuation "
                + "equals F at its canonical class. The induction groups actual compatible pair rows by their "
                + "successor class. It does not presume a scalar count identity or fit a recurrence. The unfinished "
                + "scanner sector and anchored initial multiplicities are handled below.", DescribeRole.Theorem),
            Node("literal_canonical_bridge", "Original literal count at every positive height", "For every natural m, "
                + "the individual-array count at height m plus one equals 16 times 128 to the power m plus "
                + "32 times the sum of F at m over all sixteen actual canonical boundaries. "
                + "The unfinished scanner has seen colour one but not colour two. Its boundary is one of the "
                + "two alternating words on labels zero and one. There is exactly one compatible proper row "
                + "avoiding label two, with 128 lifts and the same suffix. Every row containing label two has "
                + "64 lifts and completes the scanner; all seven cells, including the discarded first cell, "
                + "participate in this test. Induction gives twice the unfinished continuation equal to the "
                + "completed continuation plus 128 to the power m. The anchored first-row fibres contribute "
                + "32 unfinished lifts at the alternating shape, 16 completed lifts there, and 32 completed "
                + "lifts at each other shape. These disjoint literal fibres yield the formula without an "
                + "orbit quotient. HardinA233255Recurrence proves the recurrence using an exact finite "
                + "vector certificate and unbounded polynomial propagation.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock Fact(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula FullySeen() =>
        Parenthesized(Seq(Q("Bool.true"), Comma, Sp, Q("Bool.true")));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
}
