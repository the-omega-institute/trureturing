using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class GhoshWeightedShiftRootUniquenessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/GhoshWeightedShiftRootUniqueness";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Analytic/ghoshbirbonshiojha2026weightedshift");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula S => F.Id("s");
    private static Formula T => F.Id("t");
    private static Formula Q => F.Id("q");
    private static Formula Z => F.Id("z");
    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula All(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Colon, Reals, Comma, Sp, body);
    private static Formula Parameters => Seq(S, Comma, T, Comma, Q);
    private static Formula Value => Seq(
        F.Id("g"), Underscore, Grp(Parameters), Paren(Z));
    private static Formula Polynomial => Seq(
        T, Cdot, Sp, Pow(Q, D(7)), Cdot, Sp, Pow(Z, D(8)), Plus,
        Pow(Q, D(6)), Cdot, Sp, Paren(Seq(T, Cdot, Sp, Q, Minus, D(1))),
        Cdot, Sp, Pow(Z, D(7)), Plus,
        D(3), Cdot, Sp, Pow(Q, D(5)), Cdot, Sp, Paren(Seq(Q, Minus, S)),
        Cdot, Sp, Pow(Z, D(6)), Plus,
        D(5), Cdot, Sp, Pow(Q, D(4)), Cdot, Sp, Paren(Seq(S, Cdot, Sp, Q, Minus, D(1))),
        Cdot, Sp, Pow(Z, D(5)), Plus,
        Pow(Q, D(3)), Cdot, Sp, Paren(Seq(D(7), Cdot, Sp, Q, Minus, D(9), Cdot, Sp, T)),
        Cdot, Sp, Pow(Z, D(4)), Plus,
        D(7), Cdot, Sp, Pow(Q, D(2)), Cdot, Sp, Paren(Seq(T, Cdot, Sp, Q, Minus, D(1))),
        Cdot, Sp, Pow(Z, D(3)), Plus,
        D(5), Cdot, Sp, Q, Cdot, Sp, Paren(Seq(Q, Minus, S)), Cdot, Sp, Pow(Z, D(2)), Plus,
        D(3), Cdot, Sp, Paren(Seq(S, Cdot, Sp, Q, Minus, D(1))), Cdot, Sp, Z, Plus, D(1));
    private static Formula Definition => All(Seq(Parameters, Comma, Z), Seq(Value, Eq, Polynomial));
    private static Formula Hypotheses => Paren(Seq(
        D(0), Lt, S, Sp, Land, Sp, D(0), Lt, T, Sp, Land, Sp,
        D(0), Lt, Q, Sp, Land, Sp, Q, Lt, D(1)));
    private static Formula Root => Paren(Seq(
        new Formula.Fraction(D(1), D(3)), Lt, Z, Sp, Land, Sp,
        Z, Lt, D(1), Sp, Land, Sp, Value, Eq, D(0)));
    private static Formula Result => All(Parameters, Seq(
        Hypotheses, Implies, Sp, Exists, Bang, Sp, Z, Colon, Reals, Comma, Sp, Root));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For positive real s and t and zero less than q less than one, the "
        + "Ghosh-Birbonshi-Ojha polynomial has a unique root between one third and one.",
        H("A unique root of the weighted-shift polynomial"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ghosh-weighted-shift-polynomial"),
                DeclarationHandle.Create(Module + ".g"),
                H("The polynomial"),
                StatementSource.FromAuthor(Disp(Definition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real parameters s, t and q, this is the degree-eight polynomial "
                    + "g in Section 2 of Ghosh, Birbonshi and Ojha. Its definition is valid "
                    + "for every real z; the root theorem below uses positive s and t and q "
                    + "strictly between zero and one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ghosh-weighted-shift-root-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Existence and uniqueness in the open interval"),
                StatementSource.FromAuthor(Disp(Result)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every pair of positive real parameters s and t and every real "
                        + "q strictly between zero and one, exactly one real z lies strictly "
                        + "between one third and one and makes the polynomial zero.")),
                    Paragraph(Text(
                        "The value at one third is positive and the value at one is negative, "
                        + "so continuity gives an interior root. At each interior root, an "
                        + "exact polynomial identity gives a strictly negative derivative. "
                        + "The cubic term in that identity is positive by its endpoint "
                        + "values and chord decomposition on zero less than c less than z squared, "
                        + "where c equals q squared times z squared.")),
                    Paragraph(Text(
                        "If two roots were ordered u less than v, the differential fence "
                        + "with constant boundary zero would keep g nonpositive between them. "
                        + "A negative derivative at v forces positive values immediately "
                        + "to its left, a contradiction. This conclusion concerns the scalar "
                        + "polynomial root; it does not identify an operator numerical radius."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ghosh-birbonshi-ojha-2026-weighted-shift-root-uniqueness"),
                    ResolutionKind.Proved)))));
}
