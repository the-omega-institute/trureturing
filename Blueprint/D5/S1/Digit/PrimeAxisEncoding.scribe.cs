using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Digit/PrimeAxisEncoding",
            "Prime-indexed canonical W rows encode positive naturals and transport multiplication to table addition."),
        H("Prime-Axis Encoding"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("prime-axis-encoding"),
                H("Prime-axis encoding is the canonical bijection"),
                LeanDefinition(
                    "D5/S1/Digit/PrimeAxisEncoding.primeAxisEncoding"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Canonical finite-support W rows on every prime axis are equivalent "
                    + "to positive natural numbers. The forward map decodes each axis "
                    + "to its prime exponent and then applies unique factorization.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-axis-table-equivalence-and-multiplication"),
                H("Prime-axis table equivalence and multiplication"),
                LeanTheorem(
                    "D5/S1/Digit/PrimeAxisEncoding.prime_axis_encoding_spec"),
                Disp(Seq(Forall, Sp, F.Id("z"), Comma, F.Id("w"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc, Operatorname, Grp(F.Id("Bijective")), Open, Operatorname, Grp(F.Id("primeAxisEncoding")), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("coe")), Underscore, Grp(Mathbb, Grp(F.Id("N"))), Open, Operatorname, Grp(F.Id("primeAxisEncoding")), Open, F.Id("z"), Close, Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, Operatorname, Grp(F.Id("normalizedTableAdd")), Open, F.Id("z"), Comma, F.Id("w"), Close, Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("w"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Finitely supported prime axes carrying canonical W rows are equivalent to positive naturals through their factorization exponents. Addition transported through this equivalence decodes exactly as multiplication.")))
            )),
[
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S1/Digit/PrimeAxisEncoding.primeAxisEncoding")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S1/Digit/PrimeAxisEncoding.prime_axis_encoding_spec")),
                    DocumentEdge.Dependency.Create(
                        GidRef.Create("D5/S1/Digit/PrimeAxisTable")),
                ]));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
