using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class StephanA005590ZeroSetCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/StephanA005590ZeroSetCharacterization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/sloane2003a005590");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeros of A005590 at multiples of three are exactly the Fibbinary indices.",
        H("Stephan's A005590 Zero-Set Characterization"),
        Blocks(
            Paragraph(Text(
                "All indices are natural numbers and the sequence r takes integer values. "
                    + "The predicate No11 recognizes natural numbers whose binary expansion "
                    + "contains no two adjacent one bits.")),
            Node(
                "r",
                "The integer sequence A005590",
                SequenceFormula(),
                "The four equations define r at zero and one, and then on every even and "
                    + "odd index. The odd branch may take negative integer values.",
                DescribeRole.Definition),
            Node(
                "No11",
                "Binary expansions without adjacent ones",
                No11Formula(),
                "Right-shifting n by j positions exposes bits j and j+1 as the two low "
                    + "bits. Their remainder modulo four is three exactly when both bits "
                    + "are one, so No11 excludes that pattern at every position.",
                DescribeRole.Definition),
            Node(
                "result",
                "Stephan's zero-set conjecture",
                ResultFormula(),
                "A strong-induction invariant for each adjacent pair (r(n),r(n+1)) "
                    + "shows that the pair is nonzero and controls the sign of "
                    + "r(n)(r(n)-r(n+1)). It yields the zero-set classification modulo "
                    + "four. The corresponding add-a-bit classification for No11 then "
                    + "proves the equivalence for every natural n. This establishes only "
                    + "the zero-set equivalence; no growth-rate formula or further partial "
                    + "recurrence is asserted.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a005590-zero-set-fibbinary-characterization"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a005590-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        role is DescribeRole.Definition
            ? AssessedProvenance.FromLiterature(Source)
            : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula SequenceFormula()
    {
        Formula zero = Equal(R(D(0)), D(0));
        Formula one = Equal(R(D(1)), D(1));
        Formula even = ForAll(new[] { Bound("n") },
            Equal(R(Mul(D(2), N())), R(N())));
        Formula odd = ForAll(new[] { Bound("n") },
            Equal(
                R(Add(Mul(D(2), N()), D(1))),
                Subtract(R(Add(N(), D(1))), R(N()))));
        return Disp(Parenthesized(And(zero, And(one, And(even, odd)))));
    }

    private static Formula No11Formula() => Disp(ForAll(
        new[] { Bound("n") },
        Iff(
            Call("No11", N()),
            ForAll(
                new[] { Bound("j") },
                NotEqual(
                    new Formula.Modulo(
                        Parenthesized(Call("shiftRight", N(), J())),
                        D(4)),
                    D(3))))));

    private static Formula ResultFormula() => Disp(ForAll(
        new[] { Bound("n") },
        Iff(
            Equal(R(Mul(D(3), N())), D(0)),
            Call("No11", N()))));

    private static Formula N() => F.Id("n");
    private static Formula J() => F.Id("j");
    private static Formula R(Formula index) => Call("r", index);

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Naturals());

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(
            Seq(Operatorname, Grp(F.Id(name))),
            [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
