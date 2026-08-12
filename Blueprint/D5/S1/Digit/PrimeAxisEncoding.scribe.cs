using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Prime-indexed canonical W rows encode positive naturals and transport multiplication to table addition.",
        H("Prime-Axis Encoding"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-axis-encoding"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxisEncoding.primeAxisEncoding"),
                H("Prime-axis encoding is the canonical bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Canonical finite-support W rows on every prime axis are equivalent "
                                    + "to positive natural numbers. The forward map decodes each axis "
                                    + "to its prime exponent and then applies unique factorization."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-axis-table-equivalence-and-multiplication"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxisEncoding.prime_axis_encoding_spec"),
                H("Prime-axis table equivalence and multiplication"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("z"), Comma, F.Id("w"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc, Operatorname, Grp(F.Id("Bijective")), Open, Operatorname, Grp(F.Id("primeAxisEncoding")), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("coe")), Underscore, Grp(Mathbb, Grp(F.Id("N"))), Open, Operatorname, Grp(F.Id("primeAxisEncoding")), Open, F.Id("z"), Close, Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, Operatorname, Grp(F.Id("normalizedTableAdd")), Open, F.Id("z"), Comma, F.Id("w"), Close, Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("w"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Finitely supported prime axes carrying canonical W rows are equivalent to positive naturals through their factorization exponents. Addition transported through this equivalence decodes exactly as multiplication."))),
                DescribeRole.Theorem)),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Digit/PrimeAxisTable")),
                    ]));
}
