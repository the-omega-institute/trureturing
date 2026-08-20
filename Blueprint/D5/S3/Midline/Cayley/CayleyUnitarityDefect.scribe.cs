using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CayleyUnitarityDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-indexed Cayley operator is unitary exactly when every source zero is on the midline.",
        H("Cayley Unitarity Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-unitarity-defect-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/Cayley/CayleyUnitarityDefect."
                    + "cayley_unitarity_defect_formula"),
                H("Cayley unitarity defect formula"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, Esc,
                    Open,
                    Open, F.Id("C"), Caret, Grp(Star), F.Id("C"), Minus, F.Id("I"), Close,
                    F.Id("e"), Underscore, Grp(F.Id("n")), Eq,
                    F.Id("delta"), Underscore, Grp(F.Id("n")),
                    F.Id("e"), Underscore, Grp(F.Id("n")), Sp, Land, Sp,
                    F.Id("delta"), Underscore, Grp(F.Id("n")), Eq,
                    Vert, Sp, F.Id("c"), Underscore, Grp(F.Id("n")), Vert,
                    Caret, Grp(D(2)), Minus, D(1), Sp, Land, Sp,
                    F.Id("delta"), Underscore, Grp(F.Id("n")), Eq,
                    Frac,
                    Grp(D(1), Minus, D(2), F.Id("Re"),
                        Open, F.Id("rho"), Underscore, Grp(F.Id("n")), Close),
                    Grp(Vert, Sp, F.Id("rho"), Underscore, Grp(F.Id("n")), Vert,
                        Caret, Grp(D(2))),
                    Close, Sp, Land, Sp,
                    Open, F.Id("AllZerosOnMidline"), Open, F.Id("Z"), Close,
                        Sp, Iff, Sp, Forall, Sp, F.Id("n"), Comma,
                        Vert, Sp, F.Id("c"), Underscore, Grp(F.Id("n")), Vert, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open, F.Id("AllZerosOnMidline"), Open, F.Id("Z"), Close,
                        Sp, Iff, Sp, F.Id("C"), Caret, Grp(Star), F.Id("C"), Eq, F.Id("I"), Close,
                    Sp, Land, Sp,
                    Open, F.Id("AllZerosOnMidline"), Open, F.Id("Z"), Close,
                        Sp, Iff, Sp, Operatorname, Grp(F.Id("Unitary")), Open, F.Id("C"), Close,
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Z be the repository's exhaustive duplicate-free enumeration of "
                        + "classical zeta zeros in the open strip. For each indexed zero rho_n, "
                        + "the coefficient c_n is constructed as (rho_n - 1)/rho_n. The operator "
                        + "C is the diagonal operator with these coefficients, its star conjugates "
                        + "them coordinatewise, and e_n is the coordinate basis vector.")),
                    Paragraph(Text(
                        "On every coordinate, the star-unitarity defect sends e_n to delta_n e_n. "
                        + "The public statement identifies delta_n both as |c_n|^2 - 1 and as "
                        + "(1 - 2 Re(rho_n))/|rho_n|^2. Positivity of the real part in the source "
                        + "carrier makes every denominator nonzero.")),
                    Paragraph(Text(
                        "Consequently, all enumerated zeros lie on the real-part-one-half midline "
                        + "if and only if every Cayley coefficient has norm one, if and only if "
                        + "C* C is the identity, if and only if C has its coordinatewise star as a "
                        + "two-sided inverse. The statement covers the full countable carrier and "
                        + "does not replace it with a finite matrix or a selected zero."))),
                DescribeRole.Theorem))));
}
