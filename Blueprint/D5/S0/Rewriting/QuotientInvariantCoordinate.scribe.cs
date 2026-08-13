using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class QuotientInvariantCoordinateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "A complete invariant gives a separating coordinate on equivalence classes.",
            H("Quotient Invariant Coordinate"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("complete-invariant-gives-injective-quotient-coordinate"),
                    DeclarationHandle.Create(
                        "D5/S0/Rewriting/QuotientInvariantCoordinate."
                        + "quotient_invariant_coordinate_injective"),
                    H("Complete invariants separate quotient classes"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("alpha"), Comma, Sp, F.Id("beta"), Comma, Sp,
                        F.Id("r"), Colon, Sp, Operatorname, Grp(F.Id("Setoid")),
                        Open, F.Id("alpha"), Close, Comma, Sp,
                        F.Id("f"), Colon, Sp, F.Id("alpha"), Sp, To, Sp, F.Id("beta"),
                        Comma, Sp, Open,
                        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp,
                        F.Id("alpha"), Comma, Sp,
                        F.Id("f"), Open, F.Id("x"), Close, Sp, Eq, Sp,
                        F.Id("f"), Open, F.Id("y"), Close, Sp, Leftrightarrow, Sp,
                        F.Id("r"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                        Close, Sp, Rightarrow, Sp,
                        Operatorname, Grp(F.Id("Injective")), Open,
                        Operatorname, Grp(F.Id("QuotientLift")), Underscore,
                        F.Id("r"), Open, F.Id("f"), Close, Close, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The completeness hypothesis says that two objects have equal invariant "
                        + "values exactly when they are equivalent. Mathlib's quotient-lift "
                        + "characterization then makes the induced class coordinate injective. "
                        + "This closes only the quotient-coordinate clause; canonical "
                        + "representatives, classification examples, and metatheoretic "
                        + "self-application claims remain unresolved."))),
                    DescribeRole.Theorem))));
}
