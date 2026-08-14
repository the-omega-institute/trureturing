using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class WideVacuumBandDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite low-cost cover leaves binary records with unbounded spectrum gaps.",
        H("Wide Vacuum Band"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arbitrarily-wide-vacuum-band"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/WideVacuumBand"
                    + ".arbitrarily_wide_vacuum_band"),
                H("Finite low-cost covers leave arbitrarily wide gaps"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("c"), Underscore, D(0), Comma, Sp,
                    F.Id("c"), Underscore, D(1), InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Open, Forall, Sp, F.Id("n"), Sp, Geq, Sp, D(2), Comma, Sp,
                    Exists, Sp, F.Id("R"), Underscore, F.Id("n"), Comma, Sp,
                    Bar, F.Id("R"), Underscore, F.Id("n"), Bar, Sp, Eq, Sp, F.Id("n"),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("BinaryCoordinates")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Land, Sp,
                    F.Id("K"), Underscore, Grp(F.Id("entry")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Le, Sp, F.Id("c"), Underscore, D(0), RowBreak,
                    Land, Sp, F.Id("k"), Underscore, Grp(F.Id("min")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Geq, Sp, F.Id("n"), Sp, Minus, Sp,
                    F.Id("c"), Underscore, D(1),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("width")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Geq, Sp, F.Id("n"), Sp, Minus, Sp,
                    F.Id("c"), Underscore, D(0), Sp, Minus, Sp,
                    F.Id("c"), Underscore, D(1), Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("W"), InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Exists, Sp, F.Id("n"), Sp, Geq, Sp, D(2), Comma, Sp,
                    F.Id("R"), Underscore, F.Id("n"), Comma, Sp,
                    Bar, F.Id("R"), Underscore, F.Id("n"), Bar, Sp, Eq, Sp, F.Id("n"),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("BinaryCoordinates")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Land, Sp,
                    F.Id("K"), Underscore, Grp(F.Id("entry")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Le, Sp, F.Id("c"), Underscore, D(0),
                    Sp, Land, Sp, F.Id("k"), Underscore, Grp(F.Id("min")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close,
                    Sp, Geq, Sp, F.Id("n"), Sp, Minus, Sp,
                    F.Id("c"), Underscore, D(1), Sp, Land, Sp,
                    F.Id("W"), Sp, Le, Sp,
                    Operatorname, Grp(F.Id("width")),
                    Open, F.Id("R"), Underscore, F.Id("n"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each size n, the model supplies a finite family of admissible binary "
                        + "records. Every record has entry cost at most the fixed constant c0. "
                        + "The existing spectrum-bottom definition is the least cost of a total "
                        + "program consistent with a record.")),
                    Paragraph(Text(
                        "Every program below the fixed n - c1 threshold is listed in a finite "
                        + "family. The sum of its consistency-fiber cardinalities is strictly "
                        + "smaller than the admissible-record cardinality. Mathlib's finite-union "
                        + "cardinality bound therefore leaves an uncovered record, and its least "
                        + "consistent-program cost is at least n - c1.")),
                    Paragraph(Text(
                        "Natural-number subtraction gives width at least n - c0 - c1. Choosing n "
                        + "larger than any requested width proves unboundedness. Algorithmic "
                        + "complexity semantics and the source counting estimate remain explicit "
                        + "model premises rather than being redefined or re-proved here."))),
                DescribeRole.Theorem)),
        []));
}
