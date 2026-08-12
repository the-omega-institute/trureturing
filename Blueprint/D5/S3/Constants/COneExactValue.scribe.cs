using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class COneExactValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The c1 constant has two exact golden forms and the stated eight-decimal approximation.",
        H("Exact Value of c1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("c-one-exact-value"),
                DeclarationHandle.Create("D5/S3/Constants/COneExactValue.c_one_exact_value"),
                H("The c1 constant has its exact golden forms"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("c"), Underscore, Grp(D(1)), Sp, Eq, Sp,
                    D(2), Sqrt, Grp(D(5)), F.Id("T"), Underscore, Grp(D(0)),
                    Sp, Plus, Sp, F.Id("E"), Sp, Land, RowBreak,
                    F.Id("c"), Underscore, Grp(D(1)), Sp, Eq, Sp,
                    Frac,
                    Grp(D(7), Open, D(1), Minus, Sqrt, Grp(D(5)), Close),
                    Grp(D(2, 4)), Sp, Land, RowBreak,
                    F.Id("c"), Underscore, Grp(D(1)), Sp, Eq, Sp,
                    Minus, Frac, Grp(D(7)), Grp(D(1, 2), Varphi), Sp, Land, RowBreak,
                    Lvert, Sp, F.Id("c"), Underscore, Grp(D(1)), Sp, Minus, Sp,
                    Open, Minus, Frac, Grp(D(3, 6, 0, 5, 1, 9, 8, 3)),
                    Grp(D(1, 0, 0, 0, 0, 0, 0, 0, 0)), Close, Sp, Rvert,
                    Sp, Lt, Sp, Frac, Grp(D(1)), Grp(D(2, 0, 0, 0, 0, 0, 0, 0, 0)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here T0 is the deposited exact Sturmian-Dirichlet value "
                        + "(27 - 13 sqrt(5)) / 24, E is the canonical elementary shell "
                        + "(137 - 61 sqrt(5)) / 24, and phi is Mathlib's golden ratio. "
                        + "Thus c1 is tied to the repository's authoritative exact definitions, "
                        + "not to the older rational T0 reference center in the values catalog.")),
                    Paragraph(Text(
                        "Substitution and the identity sqrt(5)^2 = 5 give "
                        + "c1 = 7(1 - sqrt(5))/24. Rationalizing the golden-ratio denominator "
                        + "gives -7/(12 phi). Rational lower and upper bounds for sqrt(5) then "
                        + "show that the exact value is within 1/200000000 of -0.36051983, "
                        + "certifying every printed decimal place.")),
                    Paragraph(Text(
                        "A checked negative control changes the exact numerator from seven to "
                        + "eight and proves that the resulting equality is false. The source "
                        + "table records this constant across rounds 144 through 178 and notes "
                        + "its four-revision history; those are provenance metadata rather than "
                        + "additional mathematical conjuncts."))),
                DescribeRole.Theorem)),
        []));
}
